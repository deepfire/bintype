(defpackage bintype
  (:use :common-lisp :alexandria)
  (:export
   bintype defbintype parse-binary export-bintype-accessors
   enum plain sequence seek zero-terminate-string out-of-stream-absolute sref set-endianness))

(in-package :bintype)

;; This macro belongs to the wider world.
(defmacro define-evaluation-domain (domain-name (&rest evaluation-result-vars))
  (with-gensyms (table-name name lambda-list type body)
    `(progn
       (defvar ,table-name (make-hash-table))
       
       (defmacro ,(format-symbol (symbol-package domain-name) "DEFINE-~S" domain-name) (,name ,lambda-list &body ,body)
	 `(setf (gethash ',,domain-name ,,table-name)
		(lambda ,,lambda-list ,@,body)))
       
       (defmacro ,(format-symbol (symbol-package domain-name) "BIND-~S" domain-name) ((,@evaluation-result-vars) ,type &body ,body)
	 "Given a parser op invocation, deliver the appropriately specialised op 'guts'."
	 `(multiple-value-bind (,,@evaluation-result-vars) (apply (gethash ,(first ,type) ,,table-name) ,(rest ,type))
	    ,@,body)))))

(defvar *bintypes* (make-hash-table))

(eval-when (:compile-toplevel :load-toplevel :execute)
  (defclass btobj ()
    ((offset :accessor btobj-offset :initarg :offset)
     (postoffset :accessor btobj-postoffset :initarg :postoffset)
     (field :accessor btobj-field :initarg :field)
     (parent :accessor parent :initarg :parent)
     (value :accessor btobj-value :initarg :value)
     (value-fn :accessor btobj-value-fn :initarg :value-fn)))

  (defclass btcontainer (btobj)
    ((childs :accessor btcontainer-childs :initarg :childs)))

  (defun btcontainer-paved-p (container)
    (not (null (btcontainer-childs container))))

  (defclass btordered (btcontainer)
    ((dimension :accessor btordered-dimension)
     (stride :accessor btordered-stride)
     (contained-type :accessor btordered-contained-type)
     (sub-value-fn :accessor btordered-sub-value-fn)))

  (defclass btstructured (btcontainer)
    ((bintype :accessor btstructured-bintype :initarg :bintype)))

  (defclass btleaf (btcontainer)
    ())

  (defgeneric cref (container sel)
    (:documentation "Reach for a child of a BTCONTAINER.")
    (:method ((btcontainer btsequence) (sel integer))
      (elt (btcontainer-childs btcontainer) sel))
    (:method ((btcontainer btstruct) (sel symbol))
      (gethash sel (btcontainer-childs btcontainer))))

  (defgeneric (setf cref) (val container sel)
    (:documentation "Set a child of a BTCONTAINER.")
    (:method (val (btcontainer btsequence) (sel integer))
      (setf (elt (btcontainer-childs btcontainer) sel) val))
    (:method (val (btcontainer btstruct) (sel symbol))
      (setf (gethash sel (btcontainer-childs btcontainer)) val)))

  (define-evaluation-domain parser-op (in-stream-p outputs-field-p))

  (define-parser-op match (name type values &key ignore out-of-stream-offset)
    (declare (type (or integer null) out-of-stream-offset))
    (values (null out-of-stream-offset) (not ignore)))

  (define-parser-op value (name type &key ignore out-of-stream-offset)
    (declare (type (or integer null) out-of-stream-offset))
    (values (null out-of-stream-offset) (not ignore)))

  (define-evaluation-domain primitive-type (subbttype subcltype subwidth subreader))

  (defun generic-u8-reader (parse-context vector offset)
    (declare (ignore parse-context))
    (aref vector offset))

  (defun generic-u16-reader (parse-context vector offset)
    (funcall (parse-context-u16-reader parse-context) vector offset))

  (defun generic-u32-reader (parse-context vector offset)
    (funcall (parse-context-u32-reader parse-context) vector offset))

  (define-primitive-type unsigned-byte (width)
    (declare (type (member 8 16 32) width))
    (values 'btleaf `(unsigned-byte ,width) (/ width 8)
	    (case width
	      (8 #'generic-u8-reader)
	      (16 #'generic-u16-reader)
	      (32 #'generic-u32-reader))))
  
  (defun consume-zero-terminated-string (vector offset dimension)
    (let ((search-stop (min (+ offset dimension) (length vector))))
      (subseq vector offset (or (position 0 vector :start offset :end search-stop) search-stop))))
  
  (define-primitive-type zero-terminated-string (dimension)
    (values 'btleaf 'string dimension 
	    (lambda (parse-context vector offset)
	      (declare (ignore parse-context))
	      (consume-zero-terminated-string vector string offset))))
  
  ;; subtype evaluation done that naively can break, when the subtype is of any complexity worth mentioning...
  ;; although, it seems to be closer than the previous attempts...
  (define-primitive-type vector (dimension &key element-type stride)
    (bind-primitive-type (subbttype subcltype subwidth subreader) element-type
      (values 'btsequence `(vector ,subcltype) (* dimension stride)
	      (lambda (parse-context vector offset)
		(let ((vector (make-array dimension :element-type subcltype)))
		  (loop :for offt :from offset :by stride :below dimension 
		        :for i :from 0 :do
		     (setf (aref vector i) (funcall subreader parse-context vector offt))))))))

  (define-primitive-type list (dimension &key element-type stride)
    (bind-primitive-type (subbttype subcltype subwidth subreader) element-type
      (values 'btsequence `(vector ,subcltype) (* dimension stride)
	      (lambda (parse-context vector offset)
		(loop :for offt :from offset :by stride :below dimension 
		      :for i :from 0
		   :collect (funcall subreader parse-context vector offt))))))

  (defstruct field
    op name typespec params
    type-name
    ;; deduced
    setter accessor-name type)

  (defmethod make-load-form ((field field) &optional env)
    (make-load-form-saving-slots field :environment env))

  (defmethod print-object ((field field) stream)
    (format stream "#S(BINTYPE::FIELD NAME: ~S METHOD: ~S SPEC: ~S)"
	    (field-name fspec) (field-sem fspec) (field-spec field)))

  (defstruct bintype
    (name nil :type symbol)
    (documentation nil :type string)
    instantiator
    parser
    fields)

  (defun bintype (name)
    (declare (type symbol name))
    (let ((ret (gethash name *bintypes*)))
      (unless ret
	(error "Unable to find the requested bintype ~S." name))
      ret))

  (defun field (bintype name)
    (find name (bintype-fields bintype) :key #'field-name))

(defun sequence-word16-le (seq offset)
  (logior (ash (elt seq (+ offset 0)) 0)
	  (ash (elt seq (+ offset 1)) 8)))

(defun sequence-word32-le (seq offset)
  (logior (ash (elt seq (+ offset 0)) 0)
	  (ash (elt seq (+ offset 1)) 8)
	  (ash (elt seq (+ offset 2)) 16)
	  (ash (elt seq (+ offset 3)) 24)))

(defun sequence-word16-be (seq offset)
  (logior (ash (elt seq (+ offset 1)) 0)
	  (ash (elt seq (+ offset 0)) 8)))

(defun sequence-word32-be (seq offset)
  (logior (ash (elt seq (+ offset 3)) 0)
	  (ash (elt seq (+ offset 2)) 8)
	  (ash (elt seq (+ offset 1)) 16)
	  (ash (elt seq (+ offset 0)) 24)))

(defun output-type-definition (name fields)
  `(defstruct ,name ,@(mapcar #'spec-field-definition fields)))

(defun output-field-accessor-registration (type-name fields-var-symbol)
  `(loop :for field :in ,fields-var-symbol
      (let* ((symbol (format-symbol (symbol-package type-name) "~A-~A"
				    type-name (field-name field))))
	(setf (field-setter field) (fdefinition (list setf symbol))
	      (field-accessor-name field) symbol))))

(defun output-bintype-instantiator-registration (name bintype-symbol)
  `(setf (bintype-instantiator ,bintype-symbol)
	 (fdefinition ',(format-symbol (symbol-package name) "MAKE-~A" name))))

(defgeneric postoffsetify (instance btobject offset)
  "Fill the POSTOFFSET slot of an OBJ, effectively performing the last step
   for making it walkable."
  (:method ((instance null) (obj btleaf) incoming)
    (setf (btobj-postoffset obj) (+ incoming (spec-leaf-width (field-spec (btobj-field obj))))))
  (:method ((instance null) (obj btordered) incoming)
    "Allocate child instances, with postoffsets calculated trivially, thanks to vector goodness."
    (setf (btobj-postoffset obj)
	  (+ incoming (loop :for i :from 0 :below (btordered-dimension obj)
			    :for offset :from incoming :by (btordered-stride obj)
			    :for postoffset :from (+ incoming (btordered-stride obj))
					    :by (btordered-stride obj) :do
			 (setf (cref obj i) (make-instance (btordered-contained-type obj)
					     :parent obj :offset offset :postoffset postoffset
					     :value-fn (btordered-sub-value-fn obj)))
		         :finally (return (* (btordered-stride obj) (btordered-dimension obj))))))))

(defun output-postoffsetify-method (name fields)
  (with-gensyms (bintype instance obj offset obj field-obj field-instance)
    `(defmethod postoffsetify ((,instance ,name) (,obj btstructured) ,offset)
       (let ((,bintype (bintype (field-type-name (btobj-field ,obj)))))
	 ,@(loop :for field :in fields :for type = (field-type field) :collect
	      `(let ((,field-obj (make-instance ',(field-object-type field) :parent ,obj
				  :bintype ,bintype :field (field ,bintype `,(field-name field))
				  :value-fn (lambda (offset) ,(field-spec field))))
		     ,field-instance)
		 ,(case (field-object-type field)
		    (btordered
		     (let ((contained-spec (spec-ordered-contained-spec spec)))
		       `(setf (btordered-stride ,field-obj) ,(spec-ordered-stride spec)
			      (btordered-dimension ,field-obj) ,(spec-ordered-dimension spec)
			      (btordered-contained-type ,field-obj) ',(spec-object-type contained-spec)
			      (btordered-sub-value-fn ,field-obj) (lambda (offset) ,contained-spec))))
		    (btstructured
		     `(let ((field-bintype (bintype ',(spec-structured-type spec))))
			(setf (btstructured-bintype ,field-obj) field-bintype
			      ,field-instance (funcall (bintype-instantiator field-bintype))
			      (btobj-value ,field-obj) ,field-instance))))
		 (setf (btobj-offset ,field-obj) ,offset
		       ,offset (postoffsetify ,field-instance ,field-obj ,offset)
		       (cref ,obj ',(field-name field)) ,field-obj)))
	 (setf (btobj-postoffset ,obj) ,offset)))))

;; The proper way is to make arrays specializable by their location in the bintype hierarchy
;; The dispatch matches CLOS badly. Let's face it. But let's get it to a workable state first.
;; How VALUE happens?
;; How array subs are traversed?

(defgeneric unserialize (btobject)
  (:method ((obj btleaf))
    (setf (btobj-value obj) (funcall (btobj-value-fn obj) (btobj-offset obj))))
  (:method ((obj btordered))
    ;; array type is too weakly specified
    (let ((array (make-array (btordered-dimension field-obj))))
      (loop :for i :from 0 :below (btordered-dimension field-obj)
	    :for suboffset :from (btobj-offset obj) :by (btordered-stride obj) :do
	 (setf (aref array i)
	       (funcall (btordered-sub-value-fn field-obj) suboffset)))
      (setf (btobj-value obj) array)))
  (:method ((obj btstructured))
    (let* ((bintype (btstructured-bintype obj))
	   (offset (btobj-offset obj)))
      (loop :for field :in (bintype-fields bintype)
            :for field-obj = (cref obj (field-name field)) :do
	 (funcall (field-setter field) (unserialize obj offset) (btobj-value obj))
	 (setf offset (btobj-postoffset field-obj)))
      (btobj-value obj))))

(defun sub (obj selector)
  (declare (type btcontainer obj))
  (unless (btcontainer-paved-p obj)
    (postoffsetify obj (btobj-offset obj)))
  (cref obj selector))

(defun value (obj)
  (or (btobj-value) (unserialize obj)))

(defun parse (bintype array &optional (offset 0))
  (let* ((instance (funcall (bintype-instantiator bintype)))
	 (btstructured (make-instance 'btstructured :bintype bintype)))
    (declare (dynamic-extent btstructured))
    (postoffsetify instance obj offset)
    (unserialize btstructured)))


(defmacro defbintype (type-name &body f)
  (let* ((documentation (cadr (assoc :documentation f)))
	 (raw-fields (cadr (assoc :fields f)))
	 (fields (loop :for (op name typespec . params) :in raw-fields :collect
		    (make-field :op op :name name :typespec typespec :params params :type-name type-name)))
	 (producing-fields (remove-if-not #'field-spec-outputs-field-p fields)))
    `(progn
       (setf (gethash ',type-name *bintypes*)
	     (make-bintype :name ',type-name :documentation ,documentation :fields ',fields))
       ,(output-type-definition type-name producing-fields)
       (define-primitive-type ,type-name ()
       (let* ((bintype (bintype ',type-name))
	      (fields (bintype-fields bintype))
	      (producing-fields (remove-if-not #'field-spec-outputs-field-p fields)))
	 ,(output-field-accessor-registration type-name 'producing-fields)
	 ,(output-bintype-instantiator-registration 'bintype)
	 ,(output-postoffsetify-method type-name fields)))))

(defun export-bintype-accessors (bintype)
  (export (list* (bintype-name bintype) (mapcar #'field-accessor-name (bintype-fields bintype)))))

(defbintype phdr
  (:documentation "ELF program header")
  (:fields
   (match type		(unsigned-byte 32)
	 		((#x0 :pt-null) (#x1 :pt-load) (#x2 :pt-dynamic) (#x3 :pt-interp)
			 (#x4 :pt-note) (#x5 :pt-shlib) (#x6 :pt-phdr) (#x7 :pt-tls)
			 (#x6474e550 :pt-gnu-eh-frame) (#x6474e551 :pt-gnu-stack)
			 (#x6474e552 :pt-gnu-relro)
			 (#x60000000 :pt-loos) (#x6fffffff :pt-hios)
			 (#x70000000 :pt-loproc) (#x7fffffff :pt-hiproc)))
   (value offt		(unsigned-byte 32))
   (value vaddr		(unsigned-byte 32))
   (value paddr		(unsigned-byte 32))
   (value filesz	(unsigned-byte 32))
   (value memsz		(unsigned-byte 32))
   (value flags		(unsigned-byte 32))
   (value align		(unsigned-byte 32)))

(defbintype shdr
  (:documentation "ELF section header")
  (:fields
   (value name	  	;(value :null-terminated-string)		;; final type
	          	;(ref (parent) 'shdr (ref (parent) 'shstrndx))	;; dependency
			(unsigned-byte 32))
   (match type		(unsigned-byte 32)
	 		((#x0 :sht-null) (#x1 :sht-progbits) (#x2 :sht-symtab)
			 (#x3 :sht-strtab) (#x4 :sht-rela) (#x5 :sht-hash)
			 (#x6 :sht-dynamic) (#x7 :sht-note) (#x8 :sht-nobits)
			 (#x9 :sht-rel) (#xa :sht-shlib) (#xb :sht-dynsym)
			 (#xe :sht-init-array) (#xf :sht-fini-array)
			 (#x10 :sht-preinit-array) (#x60000000 :sht-loos)
			 (#x6ffffff6 :sht-gnu-hash) (#x6ffffff7 :sht-gnu-liblist)
			 (#x6ffffffd :sht-gnu-verdef) (#x6ffffffe :sht-gnu-verneed)
			 (#x6fffffff :sht-gnu-versym) (#x70000000 :sht-loproc)
			 (#x7fffffff :sht-hiproc) (#x80000000 :sht-louser)
			 (#xffffffff :sht-hiuser)))
   (value flags		(unsigned-byte 32))
   (value addr		(unsigned-byte 32))
   (value offt		(unsigned-byte 32))
   (value size		(unsigned-byte 32))
   (value link		(unsigned-byte 32))
   (value info		(unsigned-byte 32))
   (value addralign	(unsigned-byte 32))
   (value entsize	(unsigned-byte 32))))

;; leaf-width
;; ordered-contained-spec, ordered-stride, ordered-dimension
;; structured-type
(defbintype ehdr
  (:documentation "ELF header")
  (:fields
   (match id-magic	(list 4 :element-type (unsigned-byte 8) :stride 1)
	 		(((#x7f #x45 #x4c #x46) t)))
   (match id-class	(unsigned-byte 8)
	 		((#x0 :none) (#x1 :32) (#x2 :64)))
   (match id-data	(unsigned-byte 8)
	 		((#x0 :none)
			 (#x1 (set-endianness :little-endian) :lsb)
			 (#x2 (set-endianness :big-endian) :msb)))
   (value id-version	(unsigned-byte 8))
   (value nil		(unsigned-byte 8) :ignore t)
   (value id-name	(unsigned-byte 8) :count 8 :stride 1 :format 'vector)
   (match type		(unsigned-byte 16)
			((#x0 :et-none) (#x1 :et-rel) (#x2 :et-exec) (#x3 :et-dyn)
			 (#x4 :et-core) (#xff00 :et-loproc) (#xffff :et-hiproc)))
   (match machine	(unsigned-byte 16)
	 		((0 :em-none) (1 :em-m32) (2 :em-sparc) (3 :em-386)
			 (4 :em-68k) (5 :em-88k) (7 :em-860) (8 :em-mips)
			 (9 :em-s370) (10 :em-mips-rs4-be) (11 :em-rs6000)
			 (15 :em-parisc) (16 :em-ncube) (17 :em-vpp500)
			 (18 :em-sparc32plus) (19 :em-960) (20 :em-ppc)
			 (36 :em-v800) (37 :em-fr20) (38 :em-rh32)
			 (39 :em-mma) (40 :em-arm) (41 :em-fake-alpha)
			 (42 :em-sh) (43 :em-sparcv9) (44 :em-tricore)
			 (45 :em-arc) (46 :em-h8-300) (47 :em-h8-300h)
			 (48 :em-h8s) (49 :em-h8-500) (50 :em-ia-64)
			 (51 :em-mips-x) (52 :em-coldfire) (53 :em-68hc12)))
   (match version	(unsigned-byte 32)
			((0 :none) (1 :1)))
   (value entry		(unsigned-byte 32))
   (value phoff		(unsigned-byte 32))
   (value shoff		(unsigned-byte 32))
   (value flags		(unsigned-byte 32))
   (value ehsize	(unsigned-byte 16))
   (value phentsize	(unsigned-byte 16))
   (value phnum		(unsigned-byte 16))
   (value shentsize	(unsigned-byte 16))
   (value shnum		(unsigned-byte 16))
   (value shstrndx	(unsigned-byte 16))
   (value phdrs		(list (value (sub (self) 'phnum)) :element-type 'phdr :stride (value (sub (self) 'phentsize)))
	  		:out-of-stream-offset (sref 'phoff))
   (value phdrs		(list (value (sub (self) 'shnum)) :element-type 'shdr :stride (value (sub (self) 'shentsize)))
	  		:out-of-stream-offset (sref 'shoff)))

;; (mapc (compose #'export-bintype-accessors #'bintype) '(ehdr phdr shdr))

;; (let ((test-file-name "/bin/ls"))
;;   (format t "testing ~S:~%~S~%"
;; 	  test-file-name
;; 	  (with-open-file (str test-file-name :element-type '(unsigned-byte 8))
;; 	    (let ((seq (captured-stream:make-captured-stream str)))
;; 	      (parse-binary seq (bintype 'ehdr))))))
