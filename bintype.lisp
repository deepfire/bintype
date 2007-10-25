(defpackage bintype
  (:use :common-lisp :alexandria :pergamum)
  (:export
   #:bintype #:defbintype #:parse #:export-bintype-accessors
   #:match #:plain
   #:self #:parent #:sub #:value))

(in-package :bintype)

(defvar *bintypes* (make-hash-table))

  (defclass btobj ()
    ((offset :accessor btobj-offset :initarg :offset)
     (parent :accessor parent :initarg :parent)
     (width-fn :accessor btobj-width-fn :initarg :width-fn)
     (value :accessor btobj-value :initarg :value)))

  (defclass btcontainer (btobj)
    ((childs :accessor btcontainer-childs :initarg :childs)))

  (defun btcontainer-paved-p (container)
    (not (null (btcontainer-childs container))))

  (defclass btordered (btcontainer)
    ((dimension :accessor btordered-dimension :initarg :dimension)
     (stride :accessor btordered-stride :initarg :stride)
     (element-type :accessor btordered-element-type :initarg :element-type)))

  (defclass btstructured (btcontainer)
    ((bintype :accessor btstructured-bintype :initarg :bintype)
     (width-cache :accessor btstructured-width-cache :initform nil :initarg :width-cache))
    (:default-initargs
     :childs (make-hash-table)))

  (defclass btleaf (btcontainer)
    ((value-fn :accessor btleaf-value-fn :initarg :value-fn)))

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
    (emits-field-p (ignore)
      (null ignore))
    (out-of-stream-offset (out-of-stream-offset)
      out-of-stream-offset)
    (quotation ()
      '(t t &rest nil)))

  (define-evaluations toplevel-op match (name type values &key ignore out-of-stream-offset)
    (emits-field-p (ignore)
      (null ignore))
    (out-of-stream-offset (out-of-stream-offset)
      out-of-stream-offset)
    (quotation ()
      '(t t t &rest nil)))

  (define-evaluation-domain typespec)

  (defun generic-u8-reader (offset)
    (declare (special *vector*))
    (aref *vector* offset))

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
    ;; evdomain
    bttype cltype outputs-field-p
    ;; deduced
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
  (logior (ash (elt seq (+ offset 0)) 0) (ash (elt seq (+ offset 1)) 8)))
(defun sequence-word32-le (seq offset)
  (logior (ash (elt seq (+ offset 0)) 0) (ash (elt seq (+ offset 1)) 8)
	  (ash (elt seq (+ offset 2)) 16) (ash (elt seq (+ offset 3)) 24)))
(defun sequence-word16-be (seq offset)
  (logior (ash (elt seq (+ offset 1)) 0) (ash (elt seq (+ offset 0)) 8)))
(defun sequence-word32-be (seq offset)
  (logior (ash (elt seq (+ offset 3)) 0) (ash (elt seq (+ offset 2)) 8)
	  (ash (elt seq (+ offset 1)) 16) (ash (elt seq (+ offset 0)) 24)))

(defun output-field-accessor-registration (type-name fields-var-symbol)
  `(loop :for field :in (remove-if-not #'field-outputs-field-p ,fields-var-symbol) :do
      (let* ((symbol (format-symbol (symbol-package ',type-name) "~A-~A" ',type-name (field-name field))))
	(setf (field-setter field) (fdefinition `(setf ,symbol))
	      (field-accessor-name field) symbol))))

(defgeneric pave (something obj)
  (:method (something (obj btordered))
    (declare (ignore something))
    (let ((initargs (apply-typespec 'initargs (btordered-element-type obj))))
      (format t "btordered, dim, creffee: ~S ~S~%" (btordered-dimension obj) (btcontainer-childs obj))
      (loop :for i :below (btordered-dimension obj)
	    :for offset :from (btobj-offset obj) :by (btordered-stride obj) :do
	 (setf (cref obj i) (apply #'make-instance (append initargs (list :parent obj :offset offset))))))))

#| Did I begin thinking about this problem from the wrong end? -- Probably, but at the time, the problem was underspecified... 
   ... In fact implementation was a way to think about the problem. |#
(defun output-pave-method (name fields &aux (self-sym (intern "*SELF*" (symbol-package name))))
  `(defmethod pave ((instance ,name) (obj btstructured) &aux (stream-marker (btobj-offset obj)))
     (let ((,self-sym obj))
       (declare (special ,self-sym))
       ,@(loop :for field :in fields :collect
	    #| The binding construct below does not make out enough difference between
	       compile-time and runtime information. |#
	    #| DO NOT QUOTE EVERYTHING! |#
	    (let ((quoted-toplevel (lambda-xform #'quote-when (cons nil (apply-toplevel-op 'quotation (field-raw field))) (field-raw field)))
		  (quoted-typespec (lambda-xform #'quote-when (cons nil (apply-typespec 'quotation (field-typespec field))) (field-typespec field))))
	      (format t "toplevel: ~S, typespec: ~S~%" quoted-toplevel quoted-typespec)
	      `(let* (
		      (oos-offset (literal-funcall-toplevel-op out-of-stream-offset ,quoted-toplevel))
		      (initargs (literal-funcall-typespec initargs ,quoted-typespec))
		      (offset (or nil oos-offset stream-marker))
		      (field-obj (apply #'make-instance (append initargs (list :parent obj :offset offset)))))
		 (setf (cref obj ',(field-name field)) field-obj)
		 (when (typep field-obj 'btcontainer)
		   (pave (when (typep field-obj 'btstructured) (btobj-value field-obj)) field-obj))
		 (unless oos-offset
		   (incf stream-marker (funcall (btobj-width-fn field-obj))))))))))

#| Fact: during fill-value, only leaves need btobj-offset, which is of little wonder. |#
(defgeneric fill-value (btobject)
  (:method ((obj btleaf))
    (setf (btobj-value obj) (funcall (btleaf-value-fn obj) (btobj-offset obj))))
  (:method ((obj btordered)) ;; array type is too weakly specified
    (let ((array (make-array (btordered-dimension obj))))
      (map-into array #'fill-value (btcontainer-childs obj))
      array))
  (:method ((obj btstructured))
    (dolist (field (bintype-fields (btstructured-bintype obj)))
      (funcall (field-setter field) (fill-value (cref obj (field-name field))) (btobj-value obj)))
    (return-from fill-value (btobj-value obj))))

#| btstructured/btordered discrepancy! |#
(defun sub (obj selector)
  (declare (type btcontainer obj))
  (unless (btcontainer-paved-p obj)
      (pave nil obj))
  (cref obj selector))

(defun value (obj)
  (declare (type btleaf obj))
  (or (btobj-value obj) (fill-value obj)))

(defun parse (bintype *vector* &optional (offset 0) &aux *u16-reader* *u32-reader*)
  (declare (dynamic-extent btstructured) (special *u16-reader* *u32-reader* *vector*))
  (let* ((instance (funcall (bintype-instantiator bintype)))
	 (btstructured (make-instance 'btstructured :bintype bintype :value instance :offset offset)))
    (pave instance btstructured)
    (fill-value btstructured)))

(defmacro defbintype (type-name &body f)
  (flet ((analyse-field-form (toplevel)
	   (destructuring-bind (op name typespec &rest params) toplevel
	     (declare (ignore op params))
	     #| The fundamental difference between run-time and static analysis breaks it all...
	        Not for too long, hopefully. |#
	     (make-field :raw toplevel :name name :typespec typespec
			 :cltype (list 'or 'null (apply-typespec 'cl-type typespec))
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
		     :bintype bintype
		     :value (funcall (bintype-instantiator bintype)))
	             ',type-name))
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
