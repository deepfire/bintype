(defpackage bintype
  (:use :common-lisp :alexandria)
  (:export
   bintype defbintype parse-binary export-bintype-accessors
   enum plain sequence seek zero-terminate-string out-of-stream-absolute sref set-endianness))

(in-package :bintype)

(defvar *types* (make-hash-table))

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
    (:method ((btcontainer btsequence) (sel integer))
      (elt (btcontainer-childs btcontainer) sel))
    (:method ((btcontainer btstruct) (sel symbol))
      (gethash sel (btcontainer-childs btcontainer))))

  (defgeneric (setf cref) (val container sel)
    (:method (val (btcontainer btsequence) (sel integer))
      (setf (elt (btcontainer-childs btcontainer) sel) val))
    (:method (val (btcontainer btstruct) (sel symbol))
      (setf (gethash sel (btcontainer-childs btcontainer)) val)))

  (defstruct field
    name	;; as appears in the resulting type
    type-name	;; name of the containing type
    sem		;; parsed pieces
    spec	;; parsed pieces
    ext		;; parsed pieces
    setter accessor-name type parser-class)

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
    (let ((ret (gethash name *types*)))
      (unless ret
	(error "Unable to find the requested bintype ~S." name))
      ret))

  (defun field (bintype name)
    (find name (bintype-fields bintype) :key #'field-name))

  (defun sem-outputs-field-p (sem)
    (not (member sem '(:mag :pad))))

  (defun field-spec-outputs-field-p (field)
    (sem-outputs-field-p (field-sem field)))

  (defun simple-typespec-lisp-type (typespec)
    (cond ((keywordp typespec)
	   (ecase typespec
	     (:unsigned-byte-32 '(unsigned-byte 32))
	     (:unsigned-byte-16 '(unsigned-byte 16))
	     (:unsigned-byte-8 '(unsigned-byte 8))))
	  ((symbolp typespec)
	   (unless (bintype typespec)
	     (error "Reference to an inexistent binary type ~S." typespec))
	   typespec)
	  (t
	   (error "Bad type specification: ~S." typespec))))

  (defun simple-typespec-width (typespec)
    (cond ((keywordp typespec)
	   (ecase typespec
	     (:unsigned-byte-32 4)
	     (:unsigned-byte-16 2)
	     (:unsigned-byte-8 1)))
	  ((symbolp typespec)
	   (unless (bintype typespec)
	     (error "Reference to an inexistent binary type ~S." typespec))
	   typespec)
	  (t
	   (error "Bad type specification: ~S." typespec))))

  (defun spec-extract-type (spec)
    (eval `(flet ((zero-terminate-string (&rest rest)  (declare (ignorable rest)) (first rest))
		  (out-of-stream-absolute (&rest rest) (declare (ignorable rest)) (second rest))
		  (sequence (element-type &key (format 'list) &allow-other-keys)
		    (declare (ignore element-type))
		    (ecase format (vector 'simple-vector) (list 'list)))
		  (plain (&rest rest)		       (simple-typespec-lisp-type (first rest)))
		  (enum (&rest rest)		       (declare (ignorable rest)) 'keyword))
	     ,spec)))

  (defun spec-field-definition (field)
    `(,(field-field-name field) nil :type (or null ,(field-extract-type (field-spec field)))))

  (defun spec-extract-inflow-p (spec)
    (eval `(flet ((zero-terminate-string (&rest rest)  (declare (ignorable rest)) (first rest))
		  (out-of-stream-absolute (&rest rest) (declare (ignorable rest)) nil)
		  (sequence (&rest rest)	       (declare (ignorable rest)) t)
		  (plain (&rest rest)		       (declare (ignorable rest)) t)
		  (seek (&rest rest)		       (declare (ignorable rest)) t)
		  (enum (&rest rest)		       (declare (ignorable rest)) t))
	     ,spec)))

  (defun spec-extract-flowsizeform (spec)
    "Doesn't have to introduce the expression-caused dependencies: everything needed is already
     depended upon by the spec form."
    (eval `(macrolet ((zero-terminate-string (&rest rest) (first rest))
		      (sequence (typespec &key count stride &allow-other-keys)
			(declare (ignorable typespec) (type integer count stride)) 
			`(* ,count ,stride))
		      (plain (&rest rest) `(simple-typespec-width ,(first rest)))
		      (seek (&rest rest) (first rest))
		      (enum (&rest rest) `(simple-typespec-width ,(first rest))))
	     ,spec)))

  (defun spec-deduce-parser-class (spec)
    (eval `(flet ((zero-terminate-string (&rest rest)  (declare (ignorable rest)) 'btobj)
		  (out-of-stream-absolute (&rest rest) (declare (ignorable rest)) (second rest))
		  (sequence (&rest rest)	       (declare (ignorable rest)) 'btsequence)
		  (plain (&rest rest)		       (declare (ignorable rest)) 'btobj)
		  (seek (&rest rest)		       (declare (ignorable rest)) 'btobj)
		  (enum (&rest rest)		       (declare (ignorable rest)) 'btobj))
	     ,spec)))

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
  (with-gensyms (instance obj offset bintype obj field-obj field-instance)
    `(defmethod postoffsetify ((,instance ,name) (,obj btstructured) ,offset)
       (let ((,bintype (bintype (field-type-name (btobj-field ,obj)))))
	 ,@(loop :for field :in fields :for spec = (field-spec field) :collect
	      `(let ((,field-obj (make-instance ',(spec-object-type (field-spec field)) :parent ,obj
				  :bintype ,bintype :field (field ,bintype `,(field-name field))
				  :value-fn (lambda (offset) ,(field-spec field))))
		     ,field-instance)
		 ,(cond ((spec-ordered-p spec)
			 (let ((contained-spec (spec-ordered-contained-spec spec)))
			   `(setf (btordered-stride ,field-obj) ,(spec-ordered-stride spec)
				  (btordered-dimension ,field-obj) ,(spec-ordered-dimension spec)
				  (btordered-contained-type ,field-obj) ',(spec-object-type contained-spec)
				  (btordered-sub-value-fn ,field-obj) (lambda (offset) ,contained-spec))))
			((spec-structured-p spec)
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

(defun val (obj)
  (or (btobj-value) (unserialize obj)))

(defun parse (bintype array &optional (offset 0))
  (let* ((instance (funcall (bintype-instantiator bintype)))
	 (btstructured (make-instance 'btstructured :bintype bintype)))
    (declare (dynamic-extent btstructured))
    (postoffsetify instance obj offset)
    (unserialize btstructured)))

(defmacro defbintype (name docstring &body body)
  (let* ((fields (loop :for (sem field-name spec . rest) :in body :collect
		    (make-field :sem sem :name field-name :spec spec :ext rest :type-name name)))
	 (producing-fields (remove-if-not #'field-spec-outputs-field-p fields)))
    
    `(progn
       (setf (gethash ',name *types*)
	     (make-bintype :name ',name :documentation ,docstring :fields ',fields))
       ,(output-type-definition name producing-fields)
       (let* ((bintype (bintype ',name))
	      (fields (bintype-fields bintype))
	      (producing-fields (remove-if-not #'field-spec-outputs-field-p fields)))
	 ,(output-field-accessor-registration name 'producing-fields)
	 ,(output-bintype-instantiator-registration 'bintype)
	 ,(output-postoffsetify-method name fields)))))

(defun export-bintype-accessors (bintype)
  (export (list* (bintype-name bintype) (mapcar #'field-accessor-name (bintype-fields bintype)))))

;; types of object parametrisation:
;;   - offset -- for out-of-stream objects
;;   - count, stride -- for ordered containers
;;   - seek -- pads, affecting stream and therefore all further objects in named container

(defbintype phdr
    "ELF program header"
  (match type		:unsigned-byte-32
	 		((#x0 :pt-null) (#x1 :pt-load) (#x2 :pt-dynamic) (#x3 :pt-interp)
			 (#x4 :pt-note) (#x5 :pt-shlib) (#x6 :pt-phdr) (#x7 :pt-tls)
			 (#x6474e550 :pt-gnu-eh-frame) (#x6474e551 :pt-gnu-stack)
			 (#x6474e552 :pt-gnu-relro)
			 (#x60000000 :pt-loos) (#x6fffffff :pt-hios)
			 (#x70000000 :pt-loproc) (#x7fffffff :pt-hiproc)))
  (plain offt		:unsigned-byte-32)
  (plain vaddr		:unsigned-byte-32)
  (plain paddr		:unsigned-byte-32)
  (plain filesz		:unsigned-byte-32)
  (plain memsz		:unsigned-byte-32)
  (plain flags		:unsigned-byte-32)
  (plain align		:unsigned-byte-32))

;; (defbintype shdr
;;     "ELF section header"
;;   (plain	  ;(plain :null-terminated-string)		;; final type
;; 	          ;(ref (parent) 'shdr (ref (parent) 'shstrndx))	;; dependency
;; 			:unsigned-byte-32)
;;   (match type		:unsigned-byte-32
;; 	 		((#x0 :sht-null) (#x1 :sht-progbits) (#x2 :sht-symtab)
;; 			 (#x3 :sht-strtab) (#x4 :sht-rela) (#x5 :sht-hash)
;; 			 (#x6 :sht-dynamic) (#x7 :sht-note) (#x8 :sht-nobits)
;; 			 (#x9 :sht-rel) (#xa :sht-shlib) (#xb :sht-dynsym)
;; 			 (#xe :sht-init-array) (#xf :sht-fini-array)
;; 			 (#x10 :sht-preinit-array) (#x60000000 :sht-loos)
;; 			 (#x6ffffff6 :sht-gnu-hash) (#x6ffffff7 :sht-gnu-liblist)
;; 			 (#x6ffffffd :sht-gnu-verdef) (#x6ffffffe :sht-gnu-verneed)
;; 			 (#x6fffffff :sht-gnu-versym) (#x70000000 :sht-loproc)
;; 			 (#x7fffffff :sht-hiproc) (#x80000000 :sht-louser)
;; 			 (#xffffffff :sht-hiuser)))
;;   (plain flags		:unsigned-byte-32)
;;   (plain addr		:unsigned-byte-32)
;;   (plain offt		:unsigned-byte-32)
;;   (plain size		:unsigned-byte-32)
;;   (plain link		:unsigned-byte-32)
;;   (plain info		:unsigned-byte-32)
;;   (plain addralign	:unsigned-byte-32)
;;   (plain entsize	:unsigned-byte-32))

;; ;; leaf-width
;; ;; object-type     ordered, structured, leaf
;; ;; ordered-p, ordered-contained-spec, ordered-stride, ordered-dimension
;; ;; structured-p, structured-type
;; (defbintype ehdr
;;     "ELF header"
;;   (match id-magic	(sequence :unsigned-byte-8 :count 4 :stride 1 :format 'list)
;; 	 		(((#x7f #x45 #x4c #x46) t)))
;;   (match id-class	:unsigned-byte-8
;; 	 		((#x0 :none) (#x1 :32) (#x2 :64)))
;;   (match id-data	:unsigned-byte-8
;; 	 		((#x0 :none)
;; 			 (#x1 (set-endianness :little-endian) :lsb)
;; 			 (#x2 (set-endianness :big-endian) :msb)))
;;   (plain id-version	:unsigned-byte-8)
;;   (seek	 nil		1)
;;   (plain id-name	(sequence :unsigned-byte-8 :count 8 :stride 1 :format 'vector))
;;   (match type		:unsigned-byte-16
;; 			((#x0 :et-none) (#x1 :et-rel) (#x2 :et-exec) (#x3 :et-dyn)
;; 			 (#x4 :et-core) (#xff00 :et-loproc) (#xffff :et-hiproc)))
;;   (match machine	:unsigned-byte-16
;; 	 		((0 :em-none) (1 :em-m32) (2 :em-sparc) (3 :em-386)
;; 			 (4 :em-68k) (5 :em-88k) (7 :em-860) (8 :em-mips)
;; 			 (9 :em-s370) (10 :em-mips-rs4-be) (11 :em-rs6000)
;; 			 (15 :em-parisc) (16 :em-ncube) (17 :em-vpp500)
;; 			 (18 :em-sparc32plus) (19 :em-960) (20 :em-ppc)
;; 			 (36 :em-v800) (37 :em-fr20) (38 :em-rh32)
;; 			 (39 :em-mma) (40 :em-arm) (41 :em-fake-alpha)
;; 			 (42 :em-sh) (43 :em-sparcv9) (44 :em-tricore)
;; 			 (45 :em-arc) (46 :em-h8-300) (47 :em-h8-300h)
;; 			 (48 :em-h8s) (49 :em-h8-500) (50 :em-ia-64)
;; 			 (51 :em-mips-x) (52 :em-coldfire) (53 :em-68hc12)))
;;   (match version	:unsigned-byte-32
;; 			((0 :none) (1 :1)))
;;   (plain entry		:unsigned-byte-32)
;;   (plain phoff		:unsigned-byte-32)
;;   (plain shoff		:unsigned-byte-32)
;;   (plain flags		:unsigned-byte-32)
;;   (plain ehsize		:unsigned-byte-16)
;;   (plain phentsize	:unsigned-byte-16)
;;   (plain phnum		:unsigned-byte-16)
;;   (plain shentsize	:unsigned-byte-16)
;;   (plain shnum		:unsigned-byte-16)
;;   (plain shstrndx	:unsigned-byte-16)
;;   (cont  phdrs		(out-of-stream-absolute (sref 'phoff)
;; 			   (sequence 'phdr :count (sref 'phnum) :format 'list
;; 					   :stride (sref 'phentsize))))
;;   (cont  shdrs		(out-of-stream-absolute (sref 'shoff)
;; 			   (sequence 'shdr :count (sref 'shnum) :format 'list
;; 					   :stride (sref 'shentsize)))))

;; (mapc (compose #'export-bintype-accessors #'bintype) '(ehdr phdr shdr))

;; (let ((test-file-name "/bin/ls"))
;;   (format t "testing ~S:~%~S~%"
;; 	  test-file-name
;; 	  (with-open-file (str test-file-name :element-type '(unsigned-byte 8))
;; 	    (let ((seq (captured-stream:make-captured-stream str)))
;; 	      (parse-binary seq (bintype 'ehdr))))))
