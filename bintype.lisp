(defpackage bintype
  (:use :common-lisp :alexandria :pergamum :iterate)
  (:export
   #:bintype #:defbintype #:parse #:export-bintype-accessors
   #:match #:plain #:indirect #:zero-terminated-string #:zero-terminated-symbol
   #:set-endianness #:offset #:parent #:sub #:value))

(in-package :bintype)

(defvar *bintypes* (make-hash-table))

(defclass btobj ()
  ((offset :accessor offset :initarg :offset)
   (parent :accessor parent :initarg :parent)
   (toplevel :accessor toplevel :initarg :toplevel)
   (width :accessor width :initarg :width)
   (initial-to-final-fn :accessor initial-to-final-fn :initarg :initial-to-final-fn)
   (initial-value :accessor initial-value :initarg :initial-value)
   (final-value :accessor final-value :initarg :final-value)))

(defclass btcontainer (btobj)
  ((childs :accessor btcontainer-childs :initarg :childs)))

(defclass btordered (btcontainer)
  ((dimension :accessor btordered-dimension :initarg :dimension)
   (stride :accessor btordered-stride :initarg :stride)
   (element-type :accessor btordered-element-type :initarg :element-type)))

(defclass btstructured (btcontainer)
  ((bintype :accessor btstructured-bintype :initarg :bintype))
  (:default-initargs
   :childs (make-hash-table)
   :initial-to-final-fn #'values))

(defclass btleaf (btobj)
  ((value-fn :accessor btleaf-value-fn :initarg :value-fn)))

;; NOTE: structural invariants.
;; 1. All btobjs are joined in the hierarchy during creation.
;; 2. All btcontainer btobjs are paved during creation.
;; 2.1 The point 2 rests on the assumption that early paving does not
;;     introduce parsing dependencies beyond those present inherently.
;; 2.2 The point 2 is satisfied strictly after point 1.
;; 2.2.1 Is it important?
;; 2.2.1.1 Consider inheritance model like the following:
;;         A
;;         |\
;;         | B  -  an already-paved, non-evaluated sub-object containing partial information about E
;;          \  
;;           C  -  the object being currently paved
;;           |\
;;           | D  -  an already-paved sub-object containing partial information about E
;;            \
;;             E  -  this object is un-paveable, unless ...

(defmethod print-object ((o btordered) s)
  (format s "#<BTORDERED {~X} offset: ~X dimension: ~D stride: ~D element-type: ~S>"
	  (sb-vm::get-lisp-obj-address o)
	  (when (slot-boundp o 'offset)
	    (offset o))
	  (btordered-dimension o) (btordered-stride o) (btordered-element-type o)))

(defmethod print-object ((o btstructured) s)
  (format s "#<BTSTRUCTURED {~X} offset: ~X bintype: ~S>"
	  (sb-vm::get-lisp-obj-address o)
	  (when (slot-boundp o 'offset)
	    (offset o))
	  (bintype-name (btstructured-bintype o))))

(defmethod print-object ((o btleaf) s)
  (format s "#<BTLEAF {~X} offset: ~X>"
	  (sb-vm::get-lisp-obj-address o)
	  (when (slot-boundp o 'offset)
	    (offset o))))

(defmethod initialize-instance :after ((obj btobj) &rest rest &key sequence-index)
  (declare (ignore rest))
  (when (and (slot-boundp obj 'parent) (parent obj))
    (setf (cref (parent obj)
		(etypecase (parent obj)
		  (btordered sequence-index)
		  (btstructured (apply-toplevel-op 'name (toplevel obj)))))
	  obj))
  (typecase obj
    (btstructured (pave (setf (initial-value obj) (funcall (bintype-instantiator (btstructured-bintype obj)))) obj))
    (btordered    (pave nil obj)))
  (when (and (slot-boundp obj 'parent) (parent obj) (typep (parent obj) 'btstructured)
	     (apply-toplevel-op 'immediate-eval (toplevel obj)))
    (fill-value obj)))

(defgeneric cref (container sel)
  (:documentation "Reach for a child of a BTCONTAINER.")
  (:method ((btcontainer btordered) (sel integer))
    (elt (btcontainer-childs btcontainer) sel))
  (:method ((btcontainer btstructured) (sel symbol))
    (let ((val (gethash sel (btcontainer-childs btcontainer))))
      (unless val
	(error "BTSTRUCTURED ~S has no field called ~S." btcontainer sel))
      val)))

(defgeneric (setf cref) (val container sel)
  (:documentation "Set a child of a BTCONTAINER.")
  (:method (val (btcontainer btordered) (sel integer))
    (setf (elt (btcontainer-childs btcontainer) sel) val))
  (:method (val (btcontainer btstructured) (sel symbol))
    (setf (gethash sel (btcontainer-childs btcontainer)) val)))

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
	  :width (/ width 8)))
  (cl-type (width)
    `(unsigned-byte ,width))
  (quotation ()
    '(nil)))
  
(defun consume-zero-terminated-string (vector offset dimension)
  (let ((search-stop (min (+ offset dimension) (length vector))))
    (coerce (iter (for i from offset below (or (position 0 vector :start offset :end search-stop) search-stop))
		  (collect (code-char (elt vector i))))
	    'string)))
  
(define-evaluations typespec zero-terminated-string (dimension)
  (initargs (dimension)
    (list 'btleaf :value-fn (lambda (offset)
			      (declare (special *vector*))
			      (consume-zero-terminated-string *vector* offset dimension))
		  :width dimension))
  (cl-type ()
    'string)
  (quotation ()
    '(nil)))

(define-evaluations typespec zero-terminated-symbol (dimension &optional (package :keyword))
  (initargs (dimension package)
    (list 'btleaf :value-fn (lambda (offset)
			      (declare (special *vector*))
			      (intern (string-upcase (consume-zero-terminated-string *vector* offset dimension)) package))
		  :width dimension))
  (cl-type (package)
    (if (eq package :keyword) 'keyword 'symbol))
  (quotation ()
    '(nil &rest nil)))

(define-evaluations typespec sequence (dimension &key element-type stride (format :list))
  (initargs (dimension element-type stride)
    (list 'btordered
	  :element-type element-type :dimension dimension :stride stride
	  :childs (make-array dimension)
	  :width (* stride dimension)))
  (cl-type (element-type format)
    (ecase format
      (:list 'list)
      (:vector `(vector ,(apply-typespec 'cl-type element-type)))))
  (quotation ()
    '(nil &key (element-type t) stride format)))
  
(defstruct bintype
  (name nil :type symbol)
  (documentation nil :type (or null string))
  instantiator
  (field-setters (make-hash-table))
  toplevels)

(defun bintype (name)
  (declare (type symbol name))
  (let ((ret (gethash name *bintypes*)))
    (unless ret
      (error "Unable to find the requested bintype ~S." name))
    ret))

(defun bintype-toplevel (bintype name)
  (find name (bintype-toplevels bintype) :key (curry #'apply-toplevel-op 'name)))

(defgeneric pave (something obj)
  (:method (something (obj btordered))
    (declare (ignore something))
    (let ((initargs (apply-typespec 'initargs (btordered-element-type obj))))
      (iter (for i below (btordered-dimension obj))
	    (for offset from (offset obj) by (btordered-stride obj))
	    (apply #'make-instance (first initargs) :offset offset :parent obj :initial-to-final-fn #'values :sequence-index i :allow-other-keys t (rest initargs))))))

(define-evaluation-domain toplevel-op)

;; circularity: emit-toplevel-pavement -> toplevel-op indirect -> e-t-p.
(defun emit-toplevel-pavement (package bintype-name toplevel &key force-specified-toplevel &aux (self-sym (intern "*SELF*" package)))
  (let ((name (apply-toplevel-op 'name toplevel))
	(typespec (apply-toplevel-op 'typespec toplevel)))
    (let ((quoted-toplevel (lambda-xform #'quote-when (cons nil (apply-toplevel-op 'quotation toplevel)) toplevel))
	  (quoted-typespec (lambda-xform #'quote-when (cons nil (apply-typespec 'quotation typespec)) (mklist typespec))))
      (with-gensyms (start-offset o-o-s-offset initargs)
	`(lambda (,start-offset)
	   (let* ((,o-o-s-offset (literal-funcall-toplevel-op out-of-stream-offset ,quoted-toplevel))
		  (,initargs (literal-funcall-typespec initargs ,quoted-typespec))
		  (field-obj (apply #'make-instance (first ,initargs) :offset (or ,o-o-s-offset ,start-offset) :parent ,self-sym
								      :toplevel ,(if force-specified-toplevel
										     `',toplevel
										     `(load-time-value (bintype-toplevel (bintype ',bintype-name) ',name)))
								      :initial-to-final-fn ,(apply-toplevel-op 'initial-to-final-xform toplevel)
								      (rest ,initargs))))
	     (values (+ ,start-offset (if ,o-o-s-offset 0 (width field-obj)))
		     field-obj)))))))
  
(defun output-pave-method (name toplevels &aux (package (symbol-package name)) (self-sym (intern "*SELF*" package)))
  `(defmethod pave ((instance ,name) (obj btstructured) &aux (,self-sym obj))
     (declare (special ,self-sym *endianness-setter*))
     (flet ((set-endianness (val)
	      (declare (type (member :little-endian :big-endian)))
	      (funcall *endianness-setter* val)))
       (declare (ignorable #'set-endianness))
       (setf (width obj)
	     (- (funcall (compose ,@(mapcar (curry #'emit-toplevel-pavement package name) (reverse toplevels))) (offset obj))
		(offset obj))))))

(define-evaluations toplevel-op value (name typespec &key ignore out-of-stream-offset)
  (name (name)					name)
  (typespec (typespec)				typespec)
  (cl-type-for-field (typespec)			`(or null ,(apply-typespec 'cl-type typespec)))
  (emits-field-p (ignore)			(null ignore))
  (out-of-stream-offset (out-of-stream-offset)	out-of-stream-offset)
  (quotation ()					'(t t &rest nil))
  (immediate-eval ()				nil)
  (initial-to-final-xform ()			'#'values))

(defun emit-match-cond/case (testform matchforms)
  (if (every (compose #'atom #'car) matchforms)
      `(case ,testform
	 ,@matchforms
	 (default (error "Value ~S didn't match any of ~S." ,testform ',matchforms)))
      (once-only (testform)
	`(cond ,@(iter (for (testval . forms) in matchforms)
		       (collect `((null (mismatch ,testform ',testval)) ,@forms)))
	       (t (error "Value ~S didn't match any of ~S." ,testform ',(mapcar #'car matchforms)))))))

(define-evaluations toplevel-op match (name typespec values &key ignore out-of-stream-offset)
  (name (name)					name)
  (typespec (typespec)				typespec)
  (cl-type-for-field ()				'(or null keyword))
  (emits-field-p (ignore)			(null ignore))
  (out-of-stream-offset (out-of-stream-offset)	out-of-stream-offset)
  (quotation ()					'(t t t &rest nil))
  (immediate-eval (values)			t)
  (initial-to-final-xform (values) 		(emit-lambda '(val obj) (list (emit-match-cond/case 'val values)) :declarations '((ignore obj)))))

(define-evaluations toplevel-op indirect (direct-typespec result-toplevel &key ignore out-of-stream-offset final-value)
  (name (result-toplevel)			(apply-toplevel-op 'name result-toplevel))
  (typespec (direct-typespec result-toplevel final-value)
	    					(if final-value
						    (apply-toplevel-op 'typespec result-toplevel)
						    direct-typespec))
  (cl-type-for-field (result-toplevel)		(apply-toplevel-op 'cl-type-for-field result-toplevel))
  (emits-field-p (ignore)			(null ignore))
  (out-of-stream-offset (out-of-stream-offset)	out-of-stream-offset)
  (quotation ()					'(t t &rest nil))
  (immediate-eval (result-toplevel)		(apply-toplevel-op 'immediate-eval result-toplevel))
  (initial-to-final-xform (result-toplevel)	(let* ((package (symbol-package (apply-toplevel-op 'name result-toplevel)))
						       (self-sym (intern "*SELF*" package)) (direct-sym (intern "*DIRECT-VALUE*" package)))
						  (with-gensyms (obj)
						   `(compose ,(apply-toplevel-op 'initial-to-final-xform result-toplevel)
							     ,(emit-lambda `(,direct-sym ,obj &aux (,self-sym (parent ,obj)))
									   `( ;; (unless (boundp ',(intern "*SELF*" package)) (error "Totally mysterious!"))
									     (fill-value (nth-value 1 (funcall ,(emit-toplevel-pavement package nil result-toplevel
																	:force-specified-toplevel t)
													       (offset ,obj)))))
									   :declarations `((special ,self-sym ,direct-sym))))))))

#| Fact: during fill-value, only leaves need offset, which is of little wonder. |#
(defgeneric fill-value (btobject)
  (:method ((obj btobj))
    (setf (final-value obj) (funcall (initial-to-final-fn obj) (initial-value obj) obj)))
  (:method ((obj btleaf))
    (setf (initial-value obj) (funcall (btleaf-value-fn obj) (offset obj)))
    (call-next-method))
  (:method ((obj btordered))
    (setf (initial-value obj) (map (apply-typespec 'cl-type (apply-toplevel-op 'typespec (toplevel obj)))
				   #'fill-value (btcontainer-childs obj)))
    (call-next-method))
  (:method ((obj btstructured))
    (let ((bintype (btstructured-bintype obj)))
      (dolist (toplevel (bintype-toplevels bintype))
	(when (apply-toplevel-op 'emits-field-p toplevel)
	  (let ((name (apply-toplevel-op 'name toplevel)))
	    (funcall (gethash name (bintype-field-setters bintype)) (fill-value (cref obj name)) (initial-value obj))))))
    (call-next-method)))
    
(defun sub (obj selector)
  (declare (type btcontainer obj))
  (cref obj selector))

(defun value (obj)
  (declare (type btleaf obj))
  (if (slot-boundp obj 'final-value)
      (final-value obj) (fill-value obj)))

(defun parse (bintype *vector* &optional (offset 0) &aux *u16-reader* *u32-reader*)
  (declare (special *u16-reader* *u32-reader* *vector*))
  (let ((*endianness-setter* (lambda (val)
			       (setf (values *u16-reader* *u32-reader*)
				     (ecase val
				       (:little-endian (values #'u8-seq-word16le #'u8-seq-word32le))
				       (:big-endian (values #'u8-seq-word16be #'u8-seq-word32be)))))))
    (declare (special *endianness-setter*))
    (fill-value (make-instance 'btstructured :bintype bintype :initial-value (funcall (bintype-instantiator bintype)) :offset offset))))

(defmacro defbintype (type-name &body f)
  (flet ((output-defstruct-field (toplevel)
	   `(,(apply-toplevel-op 'name toplevel) nil :type ,(apply-toplevel-op 'cl-type-for-field toplevel))))
    (let* ((documentation (cadr (assoc :documentation f)))
	   (toplevels (cdr (assoc :fields f)))
	   (producing-toplevels (remove-if-not (curry #'apply-toplevel-op 'emits-field-p) toplevels)))
      `(progn
	 (setf (gethash ',type-name *bintypes*)
	       (make-bintype :name ',type-name :documentation ,documentation :toplevels ',toplevels))
	 (defstruct ,type-name ,@(mapcar #'output-defstruct-field producing-toplevels))
	 (define-evaluations typespec ,type-name ()
	   (initargs () (list 'btstructured :bintype (bintype ',type-name)))
	   (cl-type ()  ',type-name)
	   (quotation))
	 (let* ((bintype (bintype ',type-name)))
	   (dolist (toplevel (bintype-toplevels bintype))
	     (when (apply-toplevel-op 'emits-field-p toplevel)
	       (let* ((field-name (apply-toplevel-op 'name toplevel))
		      (setter-name (format-symbol (symbol-package ',type-name) "~A-~A" ',type-name field-name)))
		 (setf (gethash field-name (bintype-field-setters bintype)) (fdefinition `(setf ,setter-name))))))
	   (setf (bintype-instantiator bintype)
		 (fdefinition ',(format-symbol (symbol-package type-name) "MAKE-~A" type-name)))
	   ,(output-pave-method type-name toplevels))))))

(defun export-bintype-accessors (bintype)
  (let ((bintype-name (bintype-name bintype)))
    (export (list* bintype-name
		   (iter (for toplevel in (bintype-toplevels bintype))
			 (collect (format-symbol (symbol-package bintype-name) "~A-~A" bintype-name (apply-toplevel-op 'name toplevel))))))))
