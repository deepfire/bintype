(defpackage bintype
  (:use :common-lisp :alexandria)
  (:export
   bintype defbintype parse-binary export-bintype-accessors
   enum plain sequence seek zero-terminate-string out-of-stream-absolute sref set-endianness))

(in-package :bintype)

(defvar *types* (make-hash-table))

(eval-when (:compile-toplevel :load-toplevel :execute)
  (defclass instance ()
    ((parent :accessor instance-parent)
     (subsets :accessor instance-subsets)
     (data :accessor instance-data)))

  (defstruct fieldspec
    name sem spec-form ext accessor getter setter)

  (defmethod make-load-form ((fieldspec fieldspec) &optional env)
    (make-load-form-saving-slots fieldspec :environment env))

  (defmethod print-object ((fspec fieldspec) stream)
    (format stream "#S(BINTYPE::FIELDSPEC NAME: ~S METHOD: ~S SPEC: ~S)"
	    (fieldspec-name fspec) (fieldspec-sem fspec) (fieldspec-spec-form fspec)))

  (defstruct bintype
    (name nil :type symbol)
    (documentation nil :type string)
    maker
    parser
    fieldspecs)

  (defun bintype (name)
    (declare (type symbol name))
    (let ((ret (gethash name *types*)))
      (unless ret
	(error "Unable to find the requested bintype ~S." name))
      ret))

  (defun fieldspec (bintype name)
    (find name (bintype-fieldspecs bintype) :key #'fieldspec-name))

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
	   (error "Bad type specification: ~S." typespec)))))

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

(defun parse-binary (sequence bintype &optional (offset 0) parent endianness)
  (declare (type sequence sequence) (type bintype bintype) (integer offset))
  (funcall (bintype-parser bintype) sequence bintype offset parent endianness))

(defun output-parser-lambda (fieldspecs)
  "Output a bintype's parser lambda within a lexenv having BINTYPE and FIELDSPECS bound."
  `(lambda (sequence bintype &optional (offset 0) parent endianness)
     (declare (ignorable parent))
     (let* ((instance (funcall (bintype-maker bintype)))
	    (point offset) word16-accessor word32-accessor)
       (declare (special point))
       (labels ((set-endianness (new-endianness)
		  (setf (values word16-accessor word32-accessor)
			(case new-endianness
			  (:little-endian (values #'sequence-word16-le #'sequence-word32-le))
			  (:big-endian    (values #'sequence-word16-be #'sequence-word32-be)))))
		(word16-accessor (sequence offset)
		  (unless word16-accessor
		    (error "Attempt to use endian-dependent access with no endianness specified."))
		  (funcall word16-accessor sequence offset))
		(word32-accessor (sequence offset)
		  (unless word32-accessor
		    (error "Attempt to use endian-dependent access with no endianness specified."))
		  (funcall word32-accessor sequence offset))
		(sref (slot-name)
		  (funcall (fieldspec-getter (fieldspec bintype slot-name)) instance))
		(simple-access (seq offset typespec)
		  (declare (type sequence seq) (type integer offset))
		  (cond	((keywordp typespec)
			 (ecase typespec
			   (:unsigned-byte-8 (values (elt seq offset) (1+ offset)))
			   (:unsigned-byte-16 (values (word16-accessor seq offset) (+ 2 offset)))
			   (:unsigned-byte-32 (values (word32-accessor seq offset) (+ 4 offset)))))
			((symbolp typespec)
			 (parse-binary sequence (bintype typespec) offset parent endianness))
			(t (error "Botched typespec: ~S." typespec))))
		(seek (typespec)
		  (values nil (+ point typespec)))
		(plain (typespec)
		  (simple-access sequence point typespec))
		(enum (typespec alist)
		  (multiple-value-bind (value new-offset) (simple-access sequence point typespec)
		    (let ((match (cadr (assoc value alist :test #'=))))
		      (unless match
			(error "Got ~X at offset ~X, instead of an expected a value matching the enumerated set ~S."
			       value point alist))
		      (let ((match (if (consp match) match (list match))))
			(dolist (op (rest match))
			  (ecase (first op)
			    (set-endianness
			     (setf endianness (second op))
			     (set-endianness (second op)))))
			(values (first match) new-offset)))))
		(sequence (typespec &key count stride (format 'list))
		  (declare (dynamic-extent point))
		  (values
		   (ecase format
		     (vector (loop :with vector = (make-array count)
				   :for i :from 0 :below count
				   :for cur :from point :by stride
			        :do (setf (svref vector i) (simple-access sequence cur typespec))
				:finally (return vector)))
		     (list (loop :for i :from 0 :below count
				 :for cur :from point :by stride
			      :collect (simple-access sequence cur typespec))))
		   (+ point (* count stride)))))
	 (macrolet ((out-of-stream-absolute (offset form)
		      `(values (let ((point ,offset))
				 (declare (special point))
				 ,form)
			       point))
		    (zero-terminate-string (vector-form)
		      (with-gensyms (vector offset) 
			`(multiple-value-bind (,vector ,offset) ,vector-form
			   (values
			    (subseq ,vector 0 (min (1- (length ,vector)) (position 0 ,vector)))
			    ,offset)))))
	   (set-endianness endianness)
	   ,@(loop :for fieldspec :in fieldspecs :collect
		`(multiple-value-bind (value new-offset) ,(fieldspec-spec-form fieldspec)
		   (declare (ignorable value))
		   ,(ecase (fieldspec-sem fieldspec)
			   (:pad)
			   (:mag 
			    `(let ((magic ,(first (fieldspec-ext fieldspec))))
			       (when (funcall (if (typep value 'sequence)
						  #'mismatch (compose #'not #'=))
					      value magic)
				 (error "~S, offset ~S: expected ~S, got ~S."
					(bintype-name bintype) point magic value))))
			   ((:dep :imm :seq)
			    `(setf (,(fieldspec-accessor fieldspec) instance) value)))
		   (setf point new-offset)))
	   instance)))))

(defun fieldspec-outputs-field-p (fieldspec)
  (not (member (fieldspec-sem fieldspec) '(:mag :pad))))

(defun fieldspec-output-field (fieldspec)
  (let ((*break-on-signals* t))
  `(,(fieldspec-name fieldspec) nil :type
     (or null
	 ,(eval `(macrolet ((zero-terminate-string (first &rest rest) (declare (ignore rest)) first)
			    (out-of-stream-absolute (offset form) (declare (ignore offset)) form)
			    (sequence (element-type &key format &allow-other-keys)
			      (declare (ignore element-type))
			      (ecase (second format) (vector ''simple-vector) (list ''list)))
			    (plain (type)
			      `',(simple-typespec-lisp-type type))
			    (enum (type spec)
			      (declare (ignore type spec))
			      ''keyword))
		   ,(fieldspec-spec-form fieldspec)))))))
	   
(defmacro defbintype (name docstring &body body)
  (let* ((fieldspecs (loop :for (sem field-name spec-form . rest) :in body
			:collect (make-fieldspec :sem sem :name field-name :spec-form spec-form
						 :ext rest :accessor (format-symbol (symbol-package name) "~A-~A" name field-name))))
	 (producing-fieldspecs (remove-if-not #'fieldspec-outputs-field-p fieldspecs)))
    `(let* ((fieldspecs ',fieldspecs)
	    (producing-fieldspecs (remove-if-not #'fieldspec-outputs-field-p fieldspecs))
	    (bintype (make-bintype :name ',name :documentation ,docstring :fieldspecs fieldspecs)))
       (setf (gethash ',name *types*) bintype)
       (defstruct ,name ,@(mapcar #'fieldspec-output-field producing-fieldspecs))
       (loop :for fieldspec :in producing-fieldspecs
	  :do (setf (fieldspec-getter fieldspec) (fdefinition (fieldspec-accessor fieldspec))
		    (fieldspec-setter fieldspec) (fdefinition `(setf ,(fieldspec-accessor fieldspec)))))
       (setf (bintype-maker bintype)
	     (fdefinition ',(format-symbol (symbol-package name) "MAKE-~A" name))
	     (bintype-parser bintype) ,(output-parser-lambda fieldspecs)))))

(defun export-bintype-accessors (bintype)
  (export (list* (bintype-name bintype)
		 (loop :for fieldspec :in (bintype-fieldspecs bintype)
		    :when (fieldspec-getter fieldspec)
		    :collect (format-symbol t "~A-~A"
					    (bintype-name bintype)
					    (fieldspec-name fieldspec))))))

(defbintype phdr
    "ELF program header"
  (:imm	type	(enum :unsigned-byte-32
		      '((#x0 :pt-null) (#x1 :pt-load) (#x2 :pt-dynamic) (#x3 :pt-interp)
			(#x4 :pt-note) (#x5 :pt-shlib) (#x6 :pt-phdr) (#x7 :pt-tls)
			(#x6474e550 :pt-gnu-eh-frame) (#x6474e551 :pt-gnu-stack)
			(#x6474e552 :pt-gnu-relro)
			(#x60000000 :pt-loos) (#x6fffffff :pt-hios)
			(#x70000000 :pt-loproc) (#x7fffffff :pt-hiproc))))
  (:imm	offt	(plain :unsigned-byte-32))
  (:imm	vaddr	(plain :unsigned-byte-32))
  (:imm	paddr	(plain :unsigned-byte-32))
  (:imm	filesz	(plain :unsigned-byte-32))
  (:imm	memsz	(plain :unsigned-byte-32))
  (:imm	flags	(plain :unsigned-byte-32))
  (:imm	align	(plain :unsigned-byte-32)))

;; aspects:
;;  1 in-flow?
;;  1.1 yes -- effect on the flow
;;  1.2 no -- offset
;;  2 storage type
;;  3 final type
;;  4 dependency
;;  4.1 offset in the dependency

(defbintype shdr
    "ELF section header"
  (:dep	name	  ;(plain :null-terminated-string)		;; final type
	          ;(ref (parent) 'shdr (ref (parent) 'shstrndx))	;; dependency
		  (plain :unsigned-byte-32))
		  ;)
  (:imm	type	  (enum :unsigned-byte-32 '((#x0 :sht-null) (#x1 :sht-progbits) (#x2 :sht-symtab)
					    (#x3 :sht-strtab) (#x4 :sht-rela) (#x5 :sht-hash)
					    (#x6 :sht-dynamic) (#x7 :sht-note) (#x8 :sht-nobits)
					    (#x9 :sht-rel) (#xa :sht-shlib) (#xb :sht-dynsym)
					    (#xe :sht-init-array) (#xf :sht-fini-array)
					    (#x10 :sht-preinit-array) (#x60000000 :sht-loos)
					    (#x6ffffff6 :sht-gnu-hash) (#x6ffffff7 :sht-gnu-liblist)
					    (#x6ffffffd :sht-gnu-verdef) (#x6ffffffe :sht-gnu-verneed)
					    (#x6fffffff :sht-gnu-versym) (#x70000000 :sht-loproc)
					    (#x7fffffff :sht-hiproc) (#x80000000 :sht-louser)
					    (#xffffffff :sht-hiuser))))
  (:imm	flags	  (plain :unsigned-byte-32))
  (:imm	addr	  (plain :unsigned-byte-32))
  (:imm	offt	  (plain :unsigned-byte-32))
  (:imm	size	  (plain :unsigned-byte-32))
  (:imm	link	  (plain :unsigned-byte-32))
  (:imm	info	  (plain :unsigned-byte-32))
  (:imm	addralign (plain :unsigned-byte-32))
  (:imm	entsize   (plain :unsigned-byte-32)))

(defbintype ehdr
    "ELF header"
  (:mag id-magic	(sequence :unsigned-byte-8 :count 4 :stride 1 :format 'list)
			'(#x7f #x45 #x4c #x46))
  (:imm id-class	(enum :unsigned-byte-8 '((#x0 :none) (#x1 :32) (#x2 :64))))
  (:imm id-data		(enum :unsigned-byte-8 '((#x0 :none) 
						 (#x1 (:lsb (set-endianness :little-endian)))
						 (#x2 (:msb (set-endianness :big-endian))))))
  (:imm id-version	(plain :unsigned-byte-8))
  (:pad nil		(seek 1))
  (:imm id-name		(zero-terminate-string (sequence :unsigned-byte-8 :count 8 :stride 1
							 :format 'vector)))
  (:imm type		(enum :unsigned-byte-16
			      '((#x0 :et-none) (#x1 :et-rel) (#x2 :et-exec) (#x3 :et-dyn)
				(#x4 :et-core) (#xff00 :et-loproc) (#xffff :et-hiproc))))
  (:imm machine		(enum :unsigned-byte-16 '((0 :em-none) (1 :em-m32) (2 :em-sparc) (3 :em-386)
						  (4 :em-68k) (5 :em-88k) (7 :em-860) (8 :em-mips)
						  (9 :em-s370) (10 :em-mips-rs4-be) (11 :em-rs6000)
						  (15 :em-parisc) (16 :em-ncube) (17 :em-vpp500)
						  (18 :em-sparc32plus) (19 :em-960) (20 :em-ppc)
						  (36 :em-v800) (37 :em-fr20) (38 :em-rh32)
						  (39 :em-mma) (40 :em-arm) (41 :em-fake-alpha)
						  (42 :em-sh) (43 :em-sparcv9) (44 :em-tricore)
						  (45 :em-arc) (46 :em-h8-300) (47 :em-h8-300h)
						  (48 :em-h8s) (49 :em-h8-500) (50 :em-ia-64)
						  (51 :em-mips-x) (52 :em-coldfire) (53 :em-68hc12))))
  (:imm version		(enum :unsigned-byte-32 '((0 :none) (1 :1))))
  (:imm entry		(plain :unsigned-byte-32))
  (:imm phoff		(plain :unsigned-byte-32))
  (:imm shoff		(plain :unsigned-byte-32))
  (:imm flags		(plain :unsigned-byte-32))
  (:imm ehsize		(plain :unsigned-byte-16))
  (:imm phentsize	(plain :unsigned-byte-16))
  (:imm phnum		(plain :unsigned-byte-16))
  (:imm shentsize	(plain :unsigned-byte-16))
  (:imm shnum		(plain :unsigned-byte-16))
  (:imm shstrndx	(plain :unsigned-byte-16))
  (:seq phdrs		(out-of-stream-absolute (sref 'phoff)
			   (sequence 'phdr :count (sref 'phnum) :format 'list
					   :stride (sref 'phentsize))))
  (:seq shdrs		(out-of-stream-absolute (sref 'shoff)
			   (sequence 'shdr :count (sref 'shnum) :format 'list
					   :stride (sref 'shentsize)))))

(mapc (compose #'export-bintype-accessors #'bintype) '(ehdr phdr shdr))

;; (let ((test-file-name "/bin/ls"))
;;   (format t "testing ~S:~%~S~%"
;; 	  test-file-name
;; 	  (with-open-file (str test-file-name :element-type '(unsigned-byte 8))
;; 	    (let ((seq (captured-stream:make-captured-stream str)))
;; 	      (parse-binary seq (bintype 'ehdr))))))
