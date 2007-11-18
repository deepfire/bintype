(defpackage bintype
  (:use :common-lisp :alexandria :pergamum :iterate)
  (:export
   #:bintype #:define-primitive-type #:defbintype #:parse #:export-bintype-accessors
   #:match #:plain #:indirect
   #:pure #:current-offset #:zero-terminated-string #:zero-terminated-symbol #:funcstride-sequence
   #:set-endianness #:offset #:parent #:sub #:value #:path-value
   #:*self* #:*direct-value* #:*total-length*))

(in-package :bintype)

(defvar *bintypes* (make-hash-table))

(defclass btobj ()
  ((offset :accessor offset :initarg :offset)
   (parent :accessor parent :initarg :parent)
   (toplevel :accessor toplevel :initarg :toplevel)
   (sub-id :accessor sub-id :initarg :sub-id)
   (width :accessor width :initarg :width)
   (initial-to-final-fn :accessor initial-to-final-fn :initarg :initial-to-final-fn)
   (initial-value :accessor initial-value :initarg :initial-value :initform nil)
   (final-value :accessor final-value :initarg :final-value)))

(defclass btcontainer (btobj)
  ((paved-p :accessor paved-p :initform nil)
   (paving-p :accessor paving-p :initform nil)
   (childs :accessor childs :initarg :childs)))

(defclass btordered (btcontainer)
  ((dimension :accessor btordered-dimension :initarg :dimension)
   (element-type :accessor btordered-element-type :initarg :element-type)))

(defclass btfuncstride (btordered)
  ((stride-fn :accessor btfuncstride-stride-fn :initarg :stride-fn)))

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
(defun slot-value-for-print (o slot)
  (when (slot-boundp o slot) (slot-value o slot)))

(defmethod print-object ((o btfuncstride) s)
  (format s "#<BTFUNCSTRIDE sub-id: ~S offset: ~X dimension: ~D element-type: ~S>"
	  (slot-value-for-print o 'sub-id) (slot-value-for-print o 'offset)
	  (btordered-dimension o) (btordered-element-type o)))

(defmethod print-object ((o btstructured) s)
  (format s "#<BTSTRUCTURED sub-id: ~S offset: ~X bintype: ~S>"
	  (slot-value-for-print o 'sub-id) (slot-value-for-print o 'offset)
	  (bintype-name (btstructured-bintype o))))

(defmethod print-object ((o btleaf) s)
  (format s "#<BTLEAF sub-id: ~S offset: ~X>"
	  (slot-value-for-print o 'sub-id) (slot-value-for-print o 'offset)))

(defmethod initialize-instance :after ((obj btobj) &rest rest)
  (declare (ignore rest))
  (when (and (slot-boundp obj 'parent) (parent obj))
    (setf (cref (parent obj) (sub-id obj)) obj))
  ;; We have to do it early, as PAVE dispatches upon this.
  (when (typep obj 'btstructured)
    (setf (initial-value obj) (funcall (bintype-instantiator (btstructured-bintype obj))))))

(defgeneric cref (container sel)
  (:documentation "Reach for a child of a BTCONTAINER.")
  (:method ((btcontainer btordered) (sel integer))
    (elt (childs btcontainer) sel))
  (:method ((btcontainer btstructured) (sel symbol))
    (or (gethash sel (childs btcontainer)) (error "BTSTRUCTURED ~S has no field called ~S." btcontainer sel))))

(defgeneric (setf cref) (val container sel)
  (:documentation "Set a child of a BTCONTAINER.")
  (:method (val (btcontainer btordered) (sel integer))
    (setf (elt (childs btcontainer) sel) val))
  (:method (val (btcontainer btstructured) (sel symbol))
    (setf (gethash sel (childs btcontainer)) val)))

(defun generic-u8-reader (obj)
  (declare (special *vector*))
  (elt *vector* (offset obj)))

(defun generic-u16-reader (obj)
  (declare (special *u16-reader* *vector*))
  (funcall *u16-reader* *vector* (offset obj)))

(defun generic-u32-reader (obj)
  (declare (special *u32-reader* *vector*))
  (funcall *u32-reader* *vector* (offset obj)))

(defparameter *primitive-types* (make-hash-table :test #'eq))

(defun primitive-type-p (type)
  (op-parameter-destructurer (op params) type
    (declare (ignore params))
    (gethash op *primitive-types*)))

(defmacro define-primitive-type (name lambda-list &body body)
  (let ((functions (remove-if-not (compose (curry #'eq 'defun) #'car) body))
	(macros (remove-if-not (compose (curry #'eq 'defmacro) #'car) body)))
    `(progn
       (when (primitive-type-p ',name)
	 (warn "redefining ~S in DEFINE-PRIMITIVE-TYPE" ',name))
       (setf (gethash ',name *primitive-types*) t)
       ,@(when functions
	   `((define-function-evaluations typespec ,name ,lambda-list
	       ,@(mapcar #'rest functions))))
       ,@(when macros
	   `((define-macro-evaluations typespec ,name ,lambda-list
	       ,@(mapcar #'rest macros)))))))

(define-evaluation-domain typespec)

(defun typespec-apply-meaningful-p (typespec)
  (op-parameter-destructurer (op params) typespec
    (format t "analysing ~S ~S, with s-p-t ~S -> ~S~%" op params (apply-typespec 'apply-safe-parameter-types typespec)
            (lambda-list-application-types-match-p (apply-typespec 'apply-safe-parameter-types typespec) params))
    (lambda-list-application-types-match-p (apply-typespec 'apply-safe-parameter-types typespec) params)))

(define-primitive-type unsigned-byte (width)
  (defun apply-safe-parameter-types () '((integer 0)))
  (defun constant-width (width) (/ width 8))
  (defun initargs (width)
    (list 'btleaf
	  :value-fn (case width
		      (8 #'generic-u8-reader)
		      (16 #'generic-u16-reader)
		      (32 #'generic-u32-reader))
	  :width (/ width 8)))
  (defun cl-type (width)
    `(unsigned-byte ,width))
  (defun quotation ()
    '(nil)))

(define-primitive-type pure (typespec expression)
  (defun apply-safe-parameter-types () '(t t))
  (defun constant-width () 0)
  (defmacro initargs (expression)
    `(list 'btleaf :value-fn (constantly ,expression) ;; (lambda (obj) (let ((*sub-id* (sub-id obj))) (declare (special *sub-id*)) ,expression))
	   :width 0))
  (defun cl-type (typespec)
    (apply-typespec 'cl-type typespec))
  (defun quotation ()
    '(t nil)))
  
(define-primitive-type current-offset (width)
  (defun apply-safe-parameter-types () '((integer 0)))
  (defun constant-width () 0)
  (defun initargs ()
    (list 'btleaf :value-fn (lambda (obj) (offset obj)) :width 0))
  (defun cl-type (width)
    `(unsigned-byte ,width))
  (defun quotation ()
    '(nil)))

(defun consume-zero-terminated-string (vector offset dimension)
  (let ((search-stop (min (+ offset dimension) (length vector))))
    (coerce (iter (for i from offset below (or (position 0 vector :start offset :end search-stop) search-stop))
		  (collect (code-char (elt vector i))))
	    'string)))
  
(define-primitive-type zero-terminated-string (dimension)
  (defun apply-safe-parameter-types () '((integer 0)))
  (defun constant-width (dimension) dimension)
  (defun initargs (dimension)
    (list 'btleaf :value-fn (lambda (obj)
			      (declare (special *vector*))
			      (consume-zero-terminated-string *vector* (offset obj) dimension))
		  :width dimension))
  (defun cl-type ()
    'string)
  (defun quotation ()
    '(nil)))

(define-primitive-type zero-terminated-symbol (dimension &optional (package :keyword))
  (defun apply-safe-parameter-types () '((integer 0) &optional t))
  (defun constant-width (dimension) dimension)
  (defun initargs (dimension package)
    (list 'btleaf :value-fn (lambda (obj)
			      (declare (special *vector*))
			      (intern (string-upcase (consume-zero-terminated-string *vector* (offset obj) dimension)) package))
		  :width dimension))
  (defun cl-type (package)
    (if (eq package :keyword) 'keyword 'symbol))
  (defun quotation ()
    '(nil &rest nil)))

(define-primitive-type sequence (dimension &key element-type stride stride-fn (format :list))
  (defun apply-safe-parameter-types () '((integer 0) &key (element-type t) (stride (or null (integer 0))) (stride-fn (or null function)) (format t)))
  (defun constant-width (dimension element-type stride stride-fn)
    (when-let ((constant-stride (and (null stride-fn)
                                     (or stride
                                         (and (typespec-apply-meaningful-p element-type)
                                              (apply-typespec 'constant-width element-type))))))
      (* constant-stride dimension)))
  (defun initargs (dimension element-type stride stride-fn)
    (unless (primitive-type-p element-type)
      (error "unknown sequence element type ~S." element-type))
    (let ((stride-fn (or stride-fn (when stride (constantly stride))
                         (when-let ((stride (apply-typespec 'constant-width element-type)))
                           (constantly stride))
                         (error "stride is neither specified directly, nor via stride-fn, nor it is deducible from element type."))))
      (list 'btfuncstride
            :element-type element-type :dimension dimension
            :stride-fn stride-fn
            :childs (make-array dimension :initial-element nil)
            :width (iter (for i below dimension)
                         (summing (funcall stride-fn i))))))
  (defun cl-type (element-type format)
    (ecase format
      (:list 'list)
      (:vector `(vector ,(apply-typespec 'cl-type element-type)))))
  (defun quotation ()
    '(nil &key (element-type t) stride stride-fn format)))

(define-primitive-type typecase (dispatch-value &rest types)
  (defun apply-safe-parameter-types () '(nil &rest nil))
  (defun constant-width () nil)
  (defun cl-type (types)
    `(or ,@(mapcar (compose (curry #'apply-typespec 'cl-type) #'cadr) types)))
  (defun quotation ()
    `(&rest nil))
  (defmacro initargs (dispatch-value types)
    (once-only (dispatch-value)
      `(case ,dispatch-value
	 ,@(iter (for (signature type) in types)
		 (collect `(,signature (eval-typespec initargs ,type))))
	 (t (error "no type for dispatch value ~S" ,dispatch-value))))))

(defstruct bintype
  (name nil :type symbol)
  (documentation nil :type (or null string))
  instantiator
  paver
  (field-setters (make-hash-table))
  toplevels)

(defun bintype (name)
  (declare (type symbol name))
  (or (gethash name *bintypes*) (error "Unable to find the requested bintype ~S." name)))

(defun bintype-toplevel (bintype name)
  (find name (bintype-toplevels bintype) :key (curry #'apply-toplevel-op 'name)))

(defun btstructured-constant-width (type-name)
  (let ((typespecs (mapcar (curry #'apply-toplevel-op 'typespec) (bintype-toplevels (bintype type-name)))))
    (when (every #'typespec-apply-meaningful-p typespecs)
      (reduce #'(lambda (x y) (when (and x y) (+ x y)))
              (mapcar (curry #'apply-typespec 'constant-width) typespecs)))))

(defgeneric pave (obj)
  (:method ((obj btleaf)) t)
  (:method :around ((obj btcontainer))
    (unless (or (paved-p obj) (paving-p obj))
      (setf (paving-p obj) t)
      (call-next-method)
      (setf (paving-p obj) nil
            (paved-p obj) t)))
  (:method ((obj btstructured))
    (let ((*self* obj) *total-length*)
      (declare (special *self* *total-length* *vector*))
      (setf (width obj)
            (- (funcall (funcall (bintype-paver (btstructured-bintype obj))) (offset obj)) (offset obj)))))
  (:method ((obj btordered))
    (when (and (plusp (btordered-dimension obj)) (subtypep (type-of (cref obj 0)) 'btcontainer))
      (iter (for i below (btordered-dimension obj)) (for subobj = (cref obj i))
            (pave subobj))))
  (:method ((obj btfuncstride))
    (let ((initargs (apply-typespec 'initargs (btordered-element-type obj))))
      (iter (for i below (btordered-dimension obj))
	    (for offset initially (offset obj) then (+ offset (funcall (btfuncstride-stride-fn obj) i)))
	    (apply #'make-instance (first initargs) :offset offset :parent obj :sub-id i :initial-to-final-fn #'values (rest initargs))))
    (call-next-method)))

(define-evaluation-domain toplevel-op)

;; circularity: emit-toplevel-pavement -> toplevel-op indirect -> e-t-p.
(defun emit-toplevel-pavement (package bintype-name toplevel &key force-specified-toplevel)
  (let ((name (apply-toplevel-op 'name toplevel))
	(typespec (apply-toplevel-op 'typespec toplevel)))
    (let ((quoted-toplevel (map-lambda-list #'quote-when (cons nil (apply-toplevel-op 'quotation toplevel)) toplevel))
	  (quoted-typespec (map-lambda-list #'quote-when (cons nil (apply-typespec 'quotation typespec)) (mklist typespec))))
      (with-gensyms (start-offset o-o-s-offset initargs)
        (with-named-lambda-emission (format-symbol package "~S-~S-PAVEMENT" bintype-name name) (list start-offset)
          `(declare (special *self*))
          `(let* ((,o-o-s-offset (eval-toplevel-op out-of-stream-offset ,quoted-toplevel))
                  (,initargs (eval-typespec initargs ,quoted-typespec))
                  (field-obj (apply #'make-instance (first ,initargs) :offset (or ,o-o-s-offset ,start-offset) :parent *self* :sub-id ',name
                                                                      :toplevel ,(if force-specified-toplevel
                                                                                     `',toplevel
                                                                                     `(load-time-value (bintype-toplevel (bintype ',bintype-name) ',name)))
                                                                      :initial-to-final-fn ,(apply-toplevel-op 'initial-to-final-xform toplevel)
                                                                      (rest ,initargs))))
             (pave field-obj)
             (when (and (slot-boundp field-obj 'toplevel) (apply-toplevel-op 'immediate-eval (toplevel field-obj)))
               (fill-value field-obj))
             (values (+ ,start-offset (if ,o-o-s-offset 0 (width field-obj)))
                     field-obj)))))))
  
(defun output-paver-lambda (name toplevels total-length &aux (package (symbol-package name)))
  (with-named-lambda-emission (format-symbol package "PAVE-~S" name) ()
    `(declare (special *endianness-setter* *total-length* *vector*))
    `(flet ((set-endianness (val)
              (declare (type (member :little-endian :big-endian) val))
              (funcall *endianness-setter* val)))
       (declare (ignorable #'set-endianness))
       ,@(case total-length
               (:length `((setf *total-length* (length *vector*))))
               (:array-dimension `((unless (subtypep (type-of *vector*) 'vector) (error "this bintype requires the sequence to be a vector."))
                                   (setf *total-length* (array-dimension *vector* 0))))
               ((nil))
               (t (error "total-length must be of type (member :array-dimension), was ~S." total-length)))
       (compose ,@(mapcar (curry #'emit-toplevel-pavement package name) (reverse toplevels))))))

(define-function-evaluations toplevel-op value (name typespec &key ignore out-of-stream-offset)
  (name (name)					name)
  (typespec (typespec)				typespec)
  (cl-type-for-field (typespec)			`(or null ,(apply-typespec 'cl-type typespec)))
  (emits-field-p (ignore)			(null ignore))
  (out-of-stream-offset (out-of-stream-offset)	out-of-stream-offset)
  (quotation ()					'(t t &rest nil))
  (immediate-eval ()				nil)
  (initial-to-final-xform ()			'#'values))

(defun case-able (obj)
  (typep obj '(or number symbol)))

(defun emit-match-cond/case (testform matchforms)
  (if (every (compose #'case-able #'car) matchforms)
      `(case ,testform
	 ,@matchforms
	 (t (error "Value ~S didn't match any of ~S." ,testform ',matchforms)))
      (once-only (testform)
	`(cond ,@(iter (for (testval . forms) in matchforms)
		       (collect `((null (mismatch ,testform ',testval)) ,@(or forms (list nil)))))
	       (t (error "Value ~S didn't match any of ~S." ,testform ',(mapcar #'car matchforms)))))))

(define-function-evaluations toplevel-op match (name typespec values &key ignore out-of-stream-offset)
  (name (name)					name)
  (typespec (typespec)				typespec)
  (cl-type-for-field ()				t) ;; try to calculate the most specific common type of values
  (emits-field-p (ignore)			(null ignore))
  (out-of-stream-offset (out-of-stream-offset)	out-of-stream-offset)
  (quotation ()					'(t t t &rest nil))
  (immediate-eval (values)			t)
  (initial-to-final-xform (values) 		(emit-lambda '(val obj) (list (emit-match-cond/case 'val values))
							     :declarations (emit-declarations :ignore '(obj)))))

(define-function-evaluations toplevel-op indirect (direct-typespec result-toplevel &key ignore out-of-stream-offset final-value)
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
  (initial-to-final-xform (result-toplevel)	(let* ((package (symbol-package (apply-toplevel-op 'name result-toplevel))))
						  (with-gensyms (obj)
						   `(compose ,(apply-toplevel-op 'initial-to-final-xform result-toplevel)
							     ,(emit-lambda `(*direct-value* ,obj &aux (*self* (parent ,obj)))
									   `( ;; (unless (boundp '*self*) (error "Totally mysterious!"))
									     (fill-value (nth-value 1 (funcall ,(emit-toplevel-pavement package nil result-toplevel
																	:force-specified-toplevel t)
													       (offset ,obj)))))
									   :declarations (emit-declarations :special `(*self* *direct-value*))))))))

#| Fact: during fill-value, only leaves need offset, which is of little wonder. |#
(defgeneric fill-value (btobject)
  (:method ((obj btobj))
    (setf (final-value obj) (funcall (initial-to-final-fn obj) (initial-value obj) obj)))
  (:method ((obj btleaf))
    (setf (initial-value obj) (funcall (btleaf-value-fn obj) obj))
    (call-next-method))
  (:method ((obj btordered))
    (setf (initial-value obj) (map (apply-typespec 'cl-type (apply-toplevel-op 'typespec (toplevel obj)))
				   #'fill-value (childs obj)))
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
  (unless (paved-p obj)
    (pave obj))
  (cref obj selector))

(defun value (obj)
  (declare (type btobj obj))
  (if (slot-boundp obj 'final-value)
      (final-value obj) (fill-value obj)))

(defun find-parent-by-type (base type-name)
  (labels ((iterate (current)
		    (cond ((and (typep current 'btstructured)
				(eq type-name (bintype-name (btstructured-bintype current))))
			   current)
			  ((not (slot-boundp current 'parent))
			   (error "no parent of type ~S for ~S" type-name base))
			  (t
			   (iterate (parent current))))))
    (unless (slot-boundp base 'parent)
      (error "no parent of type ~S for ~S" type-name base))
    (iterate (parent base))))

;; (defun path-value (current &rest designators)
;;   (labels ((iterate (current designators)
;; 		    (cond ((null designators)
;; 			   (value current))
;; 			  ((eq (first designators) :parent)
;; 			   (iterate (parent current) (rest designators)))
;; 			  ((and (consp (first designators)) (eq (caar designators) :typed-parent))
;; 			   (iterate (find-parent-by-type current (cadar designators)) (rest designators)))
;; 			  (t
;; 			   (iterate (sub current (first designators)) (rest designators))))))
;;     (iterate current designators)))

(defun iterator (current designators)
  (cond ((null designators)
         (value current))
        ((eq (first designators) :parent)
         (iterator (parent current) (rest designators)))
        ((and (consp (first designators)) (eq (caar designators) :typed-parent))
         (iterator (find-parent-by-type current (cadar designators)) (rest designators)))
        (t
         (iterator (sub current (first designators)) (rest designators)))))

(defun path-value (current &rest designators)
  (iterator current designators))

(defun parse (bintype *vector* &optional (endianness :little-endian) (offset 0) &aux *u16-reader* *u32-reader*)
  (declare (special *u16-reader* *u32-reader* *vector*))
  (let ((*endianness-setter* (lambda (val)
			       (setf (values *u16-reader* *u32-reader*)
				     (ecase val
				       (:little-endian (values #'u8-seq-word16le #'u8-seq-word32le))
				       (:big-endian (values #'u8-seq-word16be #'u8-seq-word32be)))))))
    (declare (special *endianness-setter*))
    (funcall *endianness-setter* endianness)
    (let ((btobj (make-instance 'btstructured :bintype bintype :offset offset)))
      (pave btobj)
      (fill-value btobj))))

(defmacro defbintype (type-name lambda-list &body f)
  (flet ((output-defstruct-field (toplevel)
	   `(,(apply-toplevel-op 'name toplevel) nil :type ,(apply-toplevel-op 'cl-type-for-field toplevel))))
    (let* ((documentation (cadr (assoc :documentation f)))
	   (total-length (cadr (assoc :total-length f)))
	   (toplevels (cdr (assoc :fields f)))
	   (producing-toplevels (remove-if-not (curry #'apply-toplevel-op 'emits-field-p) toplevels)))
      `(progn
	 (setf (gethash ',type-name *bintypes*)
	       (make-bintype :name ',type-name :documentation ,documentation :toplevels ',toplevels))
	 (defstruct ,type-name ,@(mapcar #'output-defstruct-field producing-toplevels))
	 (define-primitive-type ,type-name ,lambda-list
           (defun apply-safe-parameter-types () '(&rest (integer 0)))
	   (defun constant-width () (btstructured-constant-width ',type-name))
	   (defun initargs ,(lambda-list-binds lambda-list) (declare (ignorable ,@(lambda-list-binds lambda-list)))
                  (list 'btstructured :bintype (bintype ',type-name)))
	   (defun cl-type () ',type-name)
	   (defun quotation ()))
	 (let* ((bintype (bintype ',type-name)))
	   (dolist (toplevel (bintype-toplevels bintype))
	     (when (apply-toplevel-op 'emits-field-p toplevel)
	       (let* ((field-name (apply-toplevel-op 'name toplevel))
		      (setter-name (format-symbol (symbol-package ',type-name) "~A-~A" ',type-name field-name)))
		 (setf (gethash field-name (bintype-field-setters bintype)) (fdefinition `(setf ,setter-name))))))
	   (setf (bintype-instantiator bintype) (fdefinition ',(format-symbol (symbol-package type-name) "MAKE-~A" type-name))
                 (bintype-paver bintype) ,(output-paver-lambda type-name toplevels total-length)))))))

(defun export-bintype-accessors (bintype)
  (let ((bintype-name (bintype-name bintype)))
    (export (list* bintype-name
		   (iter (for toplevel in (bintype-toplevels bintype))
			 (collect (format-symbol (symbol-package bintype-name) "~A-~A" bintype-name (apply-toplevel-op 'name toplevel))))))))
