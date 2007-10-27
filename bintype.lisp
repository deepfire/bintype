(defpackage bintype
  (:use :common-lisp :alexandria :pergamum :iterate)
  (:export
   #:bintype #:defbintype #:parse #:export-bintype-accessors
   #:match #:plain
   #:set-endianness #:self #:parent #:sub #:value))

(in-package :bintype)

(defvar *bintypes* (make-hash-table))

(defclass btobj ()
  ((offset :accessor btobj-offset :initarg :offset)
   (parent :accessor parent :initarg :parent)
   (cl-type :accessor btobj-cl-type :initarg :cl-type)
   (width-fn :accessor btobj-width-fn :initarg :width-fn)
   (initial-to-final-fn :accessor btobj-initial-to-final-fn :initarg :initial-to-final-fn)
   (initial-value :accessor btobj-initial-value :initarg :initial-value)
   (final-value :accessor btobj-final-value :initarg :final-value)))

(defclass btcontainer (btobj)
  ((childs :accessor btcontainer-childs :initarg :childs)))

(defun btcontainer-paved-p (container)
  (not (null (btcontainer-childs container))))

(defclass btordered (btcontainer)
  ((dimension :accessor btordered-dimension :initarg :dimension)
   (stride :accessor btordered-stride :initarg :stride)
   (element-type :accessor btordered-element-type :initarg :element-type)))

(defclass btstructured (btcontainer)
  ((bintype :accessor btstructured-bintype :initarg :bintype))
  (:default-initargs
   :childs (make-hash-table)
   :initial-to-final-fn #'identity))

(defclass btleaf (btobj)
  ((value-fn :accessor btleaf-value-fn :initarg :value-fn)))

(defmethod print-object ((o btordered) s)
  (format s "#<BTORDERED {~X} offset: ~X dimension: ~D stride: ~D element-type: ~S>"
	  (sb-vm::get-lisp-obj-address o)
	  (when (slot-boundp o 'offset)
	    (btobj-offset o))
	  (btordered-dimension o) (btordered-stride o) (btordered-element-type o)))

(defmethod print-object ((o btstructured) s)
  (format s "#<BTSTRUCTURED {~X} offset: ~X bintype: ~S>"
	  (sb-vm::get-lisp-obj-address o)
	  (when (slot-boundp o 'offset)
	    (btobj-offset o))
	  (bintype-name (btstructured-bintype o))))

(defmethod print-object ((o btleaf) s)
  (format s "#<BTLEAF {~X} offset: ~X>"
	  (sb-vm::get-lisp-obj-address o)
	  (when (slot-boundp o 'offset)
	    (btobj-offset o))))

(defmethod initialize-instance :after ((obj btstructured) &rest rest)
  (declare (ignore rest))
  (setf (btobj-initial-value obj) (funcall (bintype-instantiator (btstructured-bintype obj)))))

(defgeneric cref (container sel)
  (:documentation "Reach for a child of a BTCONTAINER.")
  (:method ((btcontainer btordered) (sel integer))
    (elt (btcontainer-childs btcontainer) sel))
  (:method ((btcontainer btstructured) (sel symbol))
    (gethash sel (btcontainer-childs btcontainer))))

(defgeneric (setf cref) (val container sel)
  (:documentation "Set a child of a BTCONTAINER.")
  (:method (val (btcontainer btordered) (sel integer))
    (setf (elt (btcontainer-childs btcontainer) sel) val))
  (:method (val (btcontainer btstructured) (sel symbol))
    (setf (gethash sel (btcontainer-childs btcontainer)) val)))

(define-evaluation-domain toplevel-op)

(define-evaluations toplevel-op value (name type &key ignore out-of-stream-offset)
  (field-cl-type (type)
    `(or null ,(apply-typespec 'cl-type type)))
  (emits-field-p (ignore)
    (null ignore))
  (out-of-stream-offset (out-of-stream-offset)
    out-of-stream-offset)
  (quotation ()
    '(t t &rest nil))
  (must-evaluate-early ()
    nil)
  (initial-to-final-xform ()
    '#'identity))

(defun emit-match-cond/case (testform matchforms)
  (if (every (compose #'atom #'car) matchforms)
      `(case ,testform
	 ,@matchforms
	 (default (error "Value ~S didn't match ~S." ,testform ',matchforms)))
      (once-only (testform)
	`(cond ,@(iter (for (testval . forms) in matchforms)
		       (collect `((null (mismatch ,testform ',testval)) ,@forms)))
	       (t (error "Value ~S didn't match any of ~S." ,testform ',(mapcar #'car matchforms)))))))

(define-evaluations toplevel-op match (name type values &key ignore out-of-stream-offset)
  (field-cl-type ()
    '(or null keyword))
  (emits-field-p (ignore)
    (null ignore))
  (out-of-stream-offset (out-of-stream-offset)
    out-of-stream-offset)
  (quotation ()
    '(t t t &rest nil))
  (must-evaluate-early (values)
    t)
  (initial-to-final-xform (values)
    `(lambda (val)
       ,(emit-match-cond/case 'val values))))

(define-evaluation-domain typespec)

(defun generic-u8-reader (offset)
  (declare (special *vector*))
  (elt *vector* offset))

(defun generic-u16-reader (offset)
  (declare (special *u16-reader* *vector*))
  (funcall *u16-reader* *vector* offset))

(defun generic-u32-reader (offset)
  (declare (special *u32-reader* *vector*))
  (funcall *u32-reader* *vector* offset))

(define-evaluations typespec unsigned-byte (width)
  (initargs (width)
    (list 'btleaf
	  :value-fn (case width
		      (8 #'generic-u8-reader)
		      (16 #'generic-u16-reader)
		      (32 #'generic-u32-reader))
	  :width-fn (lambda () (/ width 8))))
  (cl-type (width)
    `(unsigned-byte ,width))
  (quotation ()
    '(nil)))
  
(defun consume-zero-terminated-string (vector offset dimension)
  (let ((search-stop (min (+ offset dimension) (length vector))))
    (subseq vector offset (or (position 0 vector :start offset :end search-stop) search-stop))))
  
(define-evaluations typespec zero-terminated-string (dimension)
  (initargs (dimension)
    (list 'btleaf
	  :value-fn (lambda (offset)
		      (declare (special *vector*))
		      (consume-zero-terminated-string *vector* offset dimension))
	  :width-fn (lambda () dimension)))
  (cl-type ()
    'string)
  (quotation ()
    '(nil)))

(define-evaluations typespec sequence (dimension &key element-type stride (format :list))
  (initargs (dimension element-type stride)
    (list 'btordered
	  :element-type element-type :dimension dimension :stride stride
	  :childs (make-array dimension)
	  :width-fn (lambda () (* stride dimension))))
  (cl-type (element-type format)
    (ecase format
      (:list 'list)
      (:vector `(vector ,(apply-typespec 'cl-type element-type)))))
  (quotation ()
    '(nil &key (element-type t) stride format)))
  
(defstruct field
  raw name typespec
  bttype cltype outputs-field-p
  setter accessor-name)

(defmethod make-load-form ((field field) &optional env)
  (make-load-form-saving-slots field :environment env))

(defmethod print-object ((field field) stream)
  (format stream "#S(BINTYPE::FIELD NAME: ~S SPEC: ~S)"
	  (field-name field) (field-typespec field)))

(defstruct bintype
  (name nil :type symbol)
  (documentation nil :type string)
  instantiator
  fields)

(defun bintype (name)
  (declare (type symbol name))
  (let ((ret (gethash name *bintypes*)))
    (unless ret
      (error "Unable to find the requested bintype ~S." name))
    ret))

(defun field (bintype name)
  (find name (bintype-fields bintype) :key #'field-name))

(defun output-field-accessor-registration (type-name fields-var-symbol)
  `(loop :for field :in (remove-if-not #'field-outputs-field-p ,fields-var-symbol) :do
      (let* ((symbol (format-symbol (symbol-package ',type-name) "~A-~A" ',type-name (field-name field))))
	(setf (field-setter field) (fdefinition `(setf ,symbol))
	      (field-accessor-name field) symbol))))

(defgeneric pave (something obj)
  (:method (something (obj btordered))
    (declare (ignore something))
    (let ((initargs (apply-typespec 'initargs (btordered-element-type obj))))
      (iter (for i below (btordered-dimension obj))
	    (for offset from (btobj-offset obj) by (btordered-stride obj))
	    (let ((sub-obj (apply #'make-instance (append initargs (list :parent obj :offset offset :initial-to-final-fn #'identity)))))
	      (setf (cref obj i) sub-obj)
	      (when (typep sub-obj 'btcontainer)
		(pave (when (typep sub-obj 'btstructured) (btobj-initial-value sub-obj)) sub-obj)))))))

#| Did I begin thinking about this problem from the wrong end? -- Probably, but at the time, the problem was underspecified... 
   ... In fact implementation was a way to think about the problem. |#
(defun output-pave-method (name fields &aux (self-sym (intern "*SELF*" (symbol-package name))))
  `(defmethod pave ((instance ,name) (obj btstructured) &aux (stream-marker (btobj-offset obj)))
     (let ((,self-sym obj))
       (declare (special ,self-sym *endianness-setter*))
       (flet ((set-endianness (val)
		(declare (type (member :little-endian :big-endian)))
		(funcall *endianness-setter* val)))
	 (declare (ignorable #'set-endianness))
	 ,@(loop :for field :in fields :collect
	      (let ((quoted-toplevel (lambda-xform #'quote-when (cons nil (apply-toplevel-op 'quotation (field-raw field))) (field-raw field)))
		    (quoted-typespec (lambda-xform #'quote-when (cons nil (apply-typespec 'quotation (field-typespec field))) (field-typespec field))))
		`(let* ((initargs (literal-funcall-typespec initargs ,quoted-typespec))
			(oos-offset (literal-funcall-toplevel-op out-of-stream-offset ,quoted-toplevel))
			(offset (or oos-offset stream-marker))
			(final-initargs (append initargs (list :parent obj :offset offset :cl-type ',(apply-typespec 'cl-type (field-typespec field))
							       :initial-to-final-fn ,(apply-toplevel-op 'initial-to-final-xform (field-raw field)))))
			(field-obj (apply #'make-instance final-initargs)))
		   (setf (cref obj ',(field-name field)) field-obj)
		   (when (typep field-obj 'btcontainer)
		     (pave (when (typep field-obj 'btstructured) (btobj-initial-value field-obj)) field-obj))
		   ,@(when (apply-toplevel-op 'must-evaluate-early (field-raw field))
			   `((fill-value field-obj)))
		   (unless oos-offset
		     (incf stream-marker (funcall (btobj-width-fn field-obj)))))))))))

#| Fact: during fill-value, only leaves need btobj-offset, which is of little wonder. |#
(defgeneric fill-value (btobject)
  (:method ((obj btobj))
    (setf (btobj-final-value obj) (funcall (btobj-initial-to-final-fn obj) (btobj-initial-value obj))))
  (:method ((obj btleaf))
    (setf (btobj-initial-value obj) (funcall (btleaf-value-fn obj) (btobj-offset obj)))
    (call-next-method))
  (:method ((obj btordered))
    (setf (btobj-initial-value obj) (map (btobj-cl-type obj) #'fill-value (btcontainer-childs obj)))
    (call-next-method))
  (:method ((obj btstructured))
    (dolist (field (bintype-fields (btstructured-bintype obj)))
      (when (field-outputs-field-p field)
	(funcall (field-setter field) (fill-value (cref obj (field-name field))) (btobj-initial-value obj))))
    (call-next-method)
    (btobj-final-value obj)))

#| btstructured/btordered discrepancy! |#
(defun sub (obj selector)
  (declare (type btcontainer obj))
  (unless (btcontainer-paved-p obj)
      (pave nil obj))
  (cref obj selector))

(defun value (obj)
  (declare (type btleaf obj))
  (if (slot-boundp obj 'final-value)
      (btobj-final-value obj) (fill-value obj)))

(defun sequence-word16le (seq offset)
  (logior (ash (elt seq (+ offset 0)) 0) (ash (elt seq (+ offset 1)) 8)))
(defun sequence-word32le (seq offset)
  (logior (ash (elt seq (+ offset 0)) 0) (ash (elt seq (+ offset 1)) 8)
	  (ash (elt seq (+ offset 2)) 16) (ash (elt seq (+ offset 3)) 24)))
(defun sequence-word16be (seq offset)
  (logior (ash (elt seq (+ offset 1)) 0) (ash (elt seq (+ offset 0)) 8)))
(defun sequence-word32be (seq offset)
  (logior (ash (elt seq (+ offset 3)) 0) (ash (elt seq (+ offset 2)) 8)
	  (ash (elt seq (+ offset 1)) 16) (ash (elt seq (+ offset 0)) 24)))

(defun parse (bintype *vector* &optional (offset 0) &aux *u16-reader* *u32-reader*)
  (declare (dynamic-extent btstructured) (special *u16-reader* *u32-reader* *vector*))
  (let* ((instance (funcall (bintype-instantiator bintype)))
	 (btstructured (make-instance 'btstructured :bintype bintype :initial-value instance :offset offset))
	 (*endianness-setter* (lambda (val)
				(setf (values *u16-reader* *u32-reader*)
				      (ecase val
					(:little-endian (values #'sequence-word16le #'sequence-word32le))
					(:big-endian (values #'sequence-word16be #'sequence-word32be)))))))
    (declare (special *endianness-setter*))
    (pave instance btstructured)
    (fill-value btstructured)))

(defmacro defbintype (type-name &body f)
  (flet ((analyse-field-form (toplevel)
	   (destructuring-bind (op name typespec &rest params) toplevel
	     (declare (ignore op params))
	     #| The fundamental difference between run-time and static analysis breaks it all...
	        Not for too long, hopefully. |#
	     (make-field :raw toplevel :name name :typespec typespec
			 :cltype (apply-toplevel-op 'field-cl-type toplevel)
			 :outputs-field-p (apply-toplevel-op 'emits-field-p toplevel))))
	 (output-defstruct-field (field)
	   `(,(field-name field) nil :type ,(field-cltype field))))
    (let* ((documentation (cadr (assoc :documentation f)))
	   (fields (mapcar #'analyse-field-form (cdr (assoc :fields f))))
	   (producing-fields (remove-if-not #'field-outputs-field-p fields)))
      `(progn
	 (setf (gethash ',type-name *bintypes*)
	       (make-bintype :name ',type-name :documentation ,documentation :fields ',fields))
	 (defstruct ,type-name ,@(mapcar #'output-defstruct-field producing-fields))
	 (define-evaluations typespec ,type-name ()
	   (initargs ()
	     (let ((bintype (bintype ',type-name)))
	       (list 'btstructured
		     :bintype bintype)))
	   (cl-type ()
	       ',type-name)
	   (quotation ()))
	 (let* ((bintype (bintype ',type-name))
		(fields (bintype-fields bintype)))
	   ,(output-field-accessor-registration type-name 'fields)
	   (setf (bintype-instantiator bintype)
		 (fdefinition ',(format-symbol (symbol-package type-name) "MAKE-~A" type-name)))
	   ,(output-pave-method type-name fields))))))

(defun export-bintype-accessors (bintype)
  (export (list* (bintype-name bintype) (mapcar #'field-accessor-name (bintype-fields bintype)))))
