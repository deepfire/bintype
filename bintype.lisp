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

  (define-lambda-parser parser-op (outputs-field-p out-of-stream-offset quote-spec))

  (define-parser-op value (name type &key ignore out-of-stream-offset)
    (declare (ignore name type);;  (type (or integer null) out-of-stream-offset)
	     )
    (values (null ignore) out-of-stream-offset '(t t &rest nil)))

  (define-parser-op match (name type values &key ignore out-of-stream-offset)
    (declare (ignore name type values);;  (type (or integer null) out-of-stream-offset)
	     )
    (values (null ignore) out-of-stream-offset '(t t t &rest nil)))

  (define-lambda-parser primitive-type (btmaker cltype quote-spec))

  (defun generic-u8-reader (offset)
    (declare (special *vector*))
    (aref *vector* offset))

  (defun generic-u16-reader (offset)
    (declare (special *u16-reader* *vector*))
    (funcall *u16-reader* *vector* offset))

  (defun generic-u32-reader (offset)
    (declare (special *u32-reader* *vector*))
    (funcall *u32-reader* *vector* offset))

  (define-primitive-type unsigned-byte (width)
    (declare (type (member 8 16 32) width))
    (values (list 'btleaf
		  :value-fn (case width
			      (8 '#'generic-u8-reader)
			      (16 '#'generic-u16-reader)
			      (32 '#'generic-u32-reader))
		  :width-fn '(lambda () (/ width 8))
		  )
	    `(unsigned-byte ,width)
	    '(nil)))
  
  (defun consume-zero-terminated-string (vector offset dimension)
    (let ((search-stop (min (+ offset dimension) (length vector))))
      (subseq vector offset (or (position 0 vector :start offset :end search-stop) search-stop))))
  
  (define-primitive-type zero-terminated-string (dimension)
    (values (list 'btleaf
		  :value-fn `(lambda (offset)
			       (declare (special *vector*))
			       (consume-zero-terminated-string *vector* offset ,dimension))
		  :width-fn `(lambda () ,dimension))
	    'string
	    '(nil)))

  (define-primitive-type vector (dimension &key element-type stride)
    (apply-bind-primitive-type (subinitargs subcltype qspec) element-type
      (declare (ignore subinitargs qspec))
      (values (list 'btordered
		    :element-type element-type
		    :dimension dimension
		    :childs (make-array dimension)
		    :stride stride
		    :width-fn `(lambda () (* ,stride ,dimension)))
	      `(vector ,subcltype)
	      '(nil &key (element-type t) stride))))

  (define-primitive-type list (dimension &key element-type stride)
    (values (list 'btordered
		  :element-type element-type
		  :dimension dimension
		  :childs (make-array dimension)
		  :stride stride
		  :width-fn `(lambda () (* ,stride ,dimension)))
	    `list
	    '(nil &key (element-type t) stride)))
  
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
    (apply-bind-primitive-type (initargs cl-type qspec) (btordered-element-type obj)
      (declare (ignorable cl-type qspec))
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
	    (apply-bind-parser-op (not-ignored out-of-stream-offset raw-quotespec) (field-raw field)
	      (declare (ignore not-ignored out-of-stream-offset))
	      (apply-bind-primitive-type (initargs cl-type type-quotespec) (field-typespec field)
		(declare (ignore initargs cl-type))
		(let ((quoted-raw (lambda-xform #'quote-when raw-quotespec (field-raw field)))
		      (quoted-type (lambda-xform #'quote-when type-quotespec (field-typespec field))))
		  (format t "raw: ~S, type: ~S~%" quoted-raw quoted-type)
		  `(funcall-bind-parser-op (not-ignored out-of-stream-offset qspec) ,quoted-raw
		     (declare (ignore not-ignored qspec))
		     (funcall-bind-primitive-type (initargs cl-type qspec) ,quoted-type
		       (declare (ignore cl-type qspec))
		       (let* ((offset (or out-of-stream-offset stream-marker))
			      (field-obj (apply #'make-instance (append initargs (list :parent obj :offset offset)))))
			 (setf (cref obj ',(field-name field)) field-obj)
			 (when (typep field-obj 'btcontainer)
			   (pave (when (typep field-obj 'btstructured) (btobj-value field-obj)) field-obj))
			 (unless out-of-stream-offset
			   (incf stream-marker (funcall (btobj-width-fn field-obj))))))))))))))

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
  (flet ((analyse-field-form (raw)
	   (destructuring-bind (op name typespec &rest params) raw
	     (declare (ignore op params))
	     (apply-bind-parser-op (outputs-field-p out-of-stream-offset qspec) raw
	       (declare (ignore out-of-stream-offset qspec))
	       (apply-bind-primitive-type (bttype cltype qspec) typespec
		 (declare (ignore qspec))
	         (make-field :raw raw :name name :typespec typespec
		   :bttype bttype :cltype (list 'or 'null cltype) :outputs-field-p outputs-field-p)))))
	 (output-defstruct-field (field)
	   `(,(field-name field) nil :type ,(field-cltype field))))
    (let* ((documentation (cadr (assoc :documentation f)))
	   (fields (mapcar #'analyse-field-form (cdr (assoc :fields f))))
	   (producing-fields (remove-if-not #'field-outputs-field-p fields)))
      `(progn
	 (setf (gethash ',type-name *bintypes*)
	       (make-bintype :name ',type-name :documentation ,documentation :fields ',fields))
	 (defstruct ,type-name ,@(mapcar #'output-defstruct-field producing-fields))
	 (define-primitive-type ,type-name ()
	   (let ((bintype (bintype ',type-name)))
	     (values (list 'btstructured
			   :bintype bintype
			   :value (funcall (bintype-instantiator bintype)))
		     ',type-name)))
	 (let* ((bintype (bintype ',type-name))
		(fields (bintype-fields bintype)))
	   ,(output-field-accessor-registration type-name 'fields)
	   (setf (bintype-instantiator bintype)
		 (fdefinition ',(format-symbol (symbol-package type-name) "MAKE-~A" type-name)))
	   ,(output-pave-method type-name fields))))))

(defun export-bintype-accessors (bintype)
  (export (list* (bintype-name bintype) (mapcar #'field-accessor-name (bintype-fields bintype)))))
