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
   (params :accessor params :initarg :params)
   (typespec :accessor typespec :initarg :typespec)
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
  (format s "#<BTFUNCSTRIDE {~8,'0X} sub-id: ~S offset: ~X dimension: ~D element-type: ~S>"
	  (sb-kernel:get-lisp-obj-address o) (slot-value-for-print o 'sub-id) (slot-value-for-print o 'offset)
	  (btordered-dimension o) (btordered-element-type o)))

(defmethod print-object ((o btstructured) s)
  (format s "#<BTSTRUCTURED sub-id: ~S offset: ~X bintype: ~S>"
	  (slot-value-for-print o 'sub-id) (slot-value-for-print o 'offset)
	  (bintype-name (btstructured-bintype o))))

(defmethod print-object ((o btleaf) s)
  (format s "#<BTLEAF {~8,'0X} sub-id: ~S offset: ~X>"
	  (sb-kernel:get-lisp-obj-address o) (slot-value-for-print o 'sub-id) (slot-value-for-print o 'offset)))

(defmethod initialize-instance :after ((obj btobj) &rest rest)
  (declare (ignore rest))
  (when (slot-boundp obj 'parent)
    (setf (cref (parent obj) (sub-id obj)) obj)))

(defmethod initialize-instance :after ((obj btordered) &rest rest)
  (declare (ignore rest))
  (setf (slot-value obj 'childs) (make-array (slot-value obj 'dimension) :initial-element nil)))

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
  (declare (special *sequence*))
  (elt *sequence* (offset obj)))

(defun generic-u16-reader (obj)
  (declare (special *u16-reader* *sequence*))
  (funcall *u16-reader* *sequence* (offset obj)))

(defun generic-u32-reader (obj)
  (declare (special *u32-reader* *sequence*))
  (funcall *u32-reader* *sequence* (offset obj)))

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

(defun typespec-types-match-p (typeset typespec)
  (op-parameter-destructurer (op params) typespec
    (declare (ignore op))
    (lambda-list-application-types-match-p (apply-typespec typeset typespec) params)))

(defun generic-typestack (typespec)
  (op-parameter-destructurer (op params) typespec
    (declare (ignore op))
    (multiple-value-bind (rest-of-typestack custom-processing) (apply-typespec 'type-paramstack typespec)
      (if custom-processing
          rest-of-typestack
          (cons (when params `(list ,@(map-lambda-list #'quote-when (apply-typespec 'quotation typespec) params))) rest-of-typestack)))))

(define-primitive-type unsigned-byte (width)
  (defun apply-safe-parameter-types () '((integer 0)))
  (defun constant-width (width) (/ width 8))
  (defun type-paramstack ())
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
  (defun type-paramstack (typespec) typespec)
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
  (defun type-paramstack ())
  (defun initargs ()
    (list 'btleaf :value-fn #'offset :width 0))
  (defun cl-type (width)
    `(unsigned-byte ,width))
  (defun quotation ()
    '(nil)))

(defun consume-zero-terminated-string (dimension obj)
  (declare (special *sequence*))
  (let ((search-stop (min (+ (offset obj) dimension) (length *sequence*))))
    (coerce (iter (for i from (offset obj) below (or (position 0 *sequence* :start (offset obj) :end search-stop) search-stop))
		  (collect (code-char (elt *sequence* i))))
	    'string)))
  
(define-primitive-type zero-terminated-string (dimension)
  (defun apply-safe-parameter-types () '((integer 0)))
  (defun constant-width (dimension) dimension)
  (defun type-paramstack ())
  (defun initargs (dimension)
    (list 'btleaf :value-fn (curry #'consume-zero-terminated-string dimension) :width dimension))
  (defun cl-type ()
    'string)
  (defun quotation ()
    '(nil)))

(define-primitive-type zero-terminated-symbol (dimension &optional (package :keyword))
  (defun apply-safe-parameter-types () '((integer 0) &optional t))
  (defun constant-width (dimension) dimension)
  (defun type-paramstack ())
  (defun initargs (dimension package)
    (list 'btleaf :value-fn (compose (the function (rcurry #'intern package)) #'string-upcase (the function (curry #'consume-zero-terminated-string dimension)))
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
                                         (and (typespec-types-match-p 'apply-safe-parameter-types element-type)
                                              (apply-typespec 'constant-width element-type))))))
      (* constant-stride dimension)))
  (defun type-paramstack (element-type)
    (generic-typestack element-type))
  (defun initargs (dimension element-type stride stride-fn)
    (unless (primitive-type-p element-type)
      (error "unknown sequence element type ~S." element-type))
    (let ((stride-fn (or stride-fn (when stride (constantly stride))
                         (when-let ((stride (and (typespec-types-match-p 'apply-safe-parameter-types element-type)
                                                 (apply-typespec 'constant-width element-type))))
                           (constantly stride))
                         (error "stride is neither specified directly, nor via stride-fn, nor it is deducible from element type."))))
      (list 'btfuncstride
            :element-type element-type :dimension dimension :stride-fn stride-fn
            :width (iter (for i below dimension)
                         (summing (funcall stride-fn i))))))
  (defun cl-type (element-type format)
    (ecase format
      (:list 'list)
      (:vector `(vector ,(apply-typespec 'cl-type element-type)))))
  (defun quotation ()
    '(nil &key (element-type t) stride stride-fn format)))

;;; Warning: DISPATCH-VALUE is the only known instance of double evaluation. Not easy to get rid of.
(define-primitive-type typecase (dispatch-value &rest types)
  (defun apply-safe-parameter-types () '(nil &rest nil))
  (defun constant-width () nil)
  (defun type-paramstack (dispatch-value types)
    (values (list (once-only (dispatch-value)
                    `(case ,dispatch-value
                       ,@(iter (for (signature type) in types)
                               (collect `(,signature ,@(generic-typestack type))))
                       (t (error "no type for dispatch value ~S" ,dispatch-value)))))
            t))
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
      (declare (special *self* *total-length* *sequence*))
      (setf (width obj)
            (- (funcall (funcall (bintype-paver (btstructured-bintype obj))) (offset obj)) (offset obj)))))
  (:method ((obj btordered))
;;     (map 'null #'pave (slot-value obj 'childs))
    (when (and (plusp (btordered-dimension obj)) (subtypep (type-of (cref obj 0)) 'btcontainer))
      (iter (for i below (btordered-dimension obj)) (for subobj = (cref obj i))
            (pave subobj))))
  (:method ((obj btfuncstride))
    (let ((typespec (btordered-element-type obj)))
      (op-parameter-destructurer (op params) typespec
        (declare (ignore params))
        (let ((initargs (apply-typespec 'initargs (cons op (second (params obj))))))
          (iter (for i below (btordered-dimension obj))
                (for offset initially (offset obj) then (+ offset (funcall (btfuncstride-stride-fn obj) i)))
                (apply #'make-instance (first initargs) :typespec typespec :offset offset :parent obj :sub-id i :initial-to-final-fn #'values :params (rest (params obj))
                       (rest initargs))))))
    (call-next-method)))

(define-evaluation-domain toplevel-op)

(defun toplevel-types-match-p (typeset toplevel)
  (op-parameter-destructurer (op params) toplevel
    (declare (ignore op))
    (lambda-list-application-types-match-p (apply-toplevel-op typeset toplevel) params)))

(defun process-field (obj immediate-p stream-offset out-of-stream-offset)
  (pave obj)
  (when immediate-p
    (fill-value obj))
  (values (+ stream-offset (if out-of-stream-offset 0 (width obj)))
          obj))

;; circularity: emit-toplevel-pavement -> toplevel-op indirect -> e-t-p.
(defun emit-toplevel-pavement (bintype-name toplevel)
  (let ((name (apply-toplevel-op 'name toplevel))
        (no-oos (toplevel-types-match-p 'no-oos toplevel))
        (typespec (apply-toplevel-op 'typespec toplevel))
        (quoted-toplevel (map-lambda-list #'quote-when (cons nil (apply-toplevel-op 'quotation toplevel)) toplevel)))
    (with-gensyms (start-offset o-o-s-offset paramstack initargs field-obj)
      (with-named-lambda-emission (format-symbol nil "~S-~S-PAVEMENT" bintype-name name) (list start-offset)
        `(declare (special *self*))
        `(let* (,@(unless no-oos `((,o-o-s-offset (eval-toplevel-op out-of-stream-offset ,quoted-toplevel))))
                (,paramstack (list ,@(generic-typestack typespec))) (,initargs (apply-typespec 'initargs (cons ',(first typespec) (first ,paramstack))))
                (,field-obj (apply #'make-instance (first ,initargs) :offset ,(if no-oos start-offset `(or ,o-o-s-offset ,start-offset)) :parent *self* :sub-id ',name
                                                                     :typespec ',typespec :initial-to-final-fn ,(apply-toplevel-op 'initial-to-final-xform toplevel)
                                                                     :params ,paramstack (rest ,initargs))))
           (process-field ,field-obj ,(apply-toplevel-op 'immediate-eval toplevel) ,start-offset ,(unless no-oos o-o-s-offset)))))))

(defun set-endianness (val)
  (declare (type (member :little-endian :big-endian) val) (special *endianness-setter*))
  (funcall *endianness-setter* val))

(defun output-paver-lambda (name toplevels total-length)
  (with-named-lambda-emission (format-symbol nil "PAVE-~S" name) ()
    `(declare (special *total-length* *sequence*))
    (case total-length
      (:length `(setf *total-length* (length *sequence*)))
      (:array-dimension `(if (subtypep (type-of *sequence*) 'vector)
                             (setf *total-length* (array-dimension *sequence* 0))
                             (error "this bintype requires the sequence to be a vector.")))
      ((nil))
      (t (error "total-length must be of type (member :array-dimension), was ~S." total-length)))
    `(compose ,@(mapcar (curry #'emit-toplevel-pavement name) (reverse toplevels)))))

(define-function-evaluations toplevel-op value (name typespec &key ignore out-of-stream-offset)
  (name (name)					name)
  (typespec (typespec)				typespec)
  (cl-type-for-field (typespec)			`(or null ,(apply-typespec 'cl-type typespec)))
  (emits-field-p (ignore)			(null ignore))
  (out-of-stream-offset (out-of-stream-offset)	out-of-stream-offset)
  (quotation ()					'(t t &rest nil))
  (no-oos ()					'(t t &key (ignore t) (out-of-stream-offset null)))
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
  (no-oos ()					'(t t t &key (ignore t) (out-of-stream-offset null)))
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
  (no-oos ()					'(t t &key (ignore t) (out-of-stream-offset null) (final-value t)))
  (immediate-eval (result-toplevel)		(apply-toplevel-op 'immediate-eval result-toplevel))
  (initial-to-final-xform (result-toplevel)	`(compose ,(apply-toplevel-op 'initial-to-final-xform result-toplevel)
                                                          ,(emit-lambda `(*direct-value* obj &aux (*self* (parent obj)))
                                                                        `((fill-value (nth-value 1 (funcall ,(emit-toplevel-pavement nil result-toplevel) (offset obj)))))
                                                                        :declarations (emit-declarations :special `(*self* *direct-value*))))))

#| Fact: during fill-value, only leaves need offset, which is of little wonder. |#
(defgeneric fill-value (btobject)
  (:method ((obj btobj))
    (setf (final-value obj) (funcall (initial-to-final-fn obj) (initial-value obj) obj)))
  (:method ((obj btleaf))
    (setf (initial-value obj) (funcall (btleaf-value-fn obj) obj))
    (call-next-method))
  (:method ((obj btordered))
    (setf (initial-value obj) (map (apply-typespec 'cl-type (typespec obj)) #'fill-value (childs obj)))
    (call-next-method))
  (:method ((obj btstructured))
    (let ((bintype (btstructured-bintype obj)))
      (setf (initial-value obj) (funcall (bintype-instantiator bintype)))
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

(defun path-value (current &rest designators)
  (labels ((iterate (current designators)
		    (cond ((null designators)
			   (value current))
			  ((eq (first designators) :parent)
			   (iterate (parent current) (rest designators)))
			  ((and (consp (first designators)) (eq (caar designators) :typed-parent))
			   (iterate (find-parent-by-type current (cadar designators)) (rest designators)))
			  (t
			   (iterate (sub current (first designators)) (rest designators))))))
    (iterate current designators)))

(defun parse (typespec *sequence* &optional (endianness :little-endian) (offset 0) &aux *u16-reader* *u32-reader*)
  (declare (special *u16-reader* *u32-reader* *sequence*))
  (let ((*endianness-setter* (lambda (val)
			       (setf (values *u16-reader* *u32-reader*)
				     (ecase val
				       (:little-endian (values #'u8-seq-word16le #'u8-seq-word32le))
				       (:big-endian (values #'u8-seq-word16be #'u8-seq-word32be)))))))
    (declare (special *endianness-setter*))
    (funcall *endianness-setter* endianness)
    (op-parameter-destructurer (op params) typespec
      (let* ((bintype (bintype op))
             (btobj (make-instance 'btstructured :bintype bintype :offset offset :params params :typespec typespec)))
        (pave btobj)
        (fill-value btobj)))))

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
           (defun type-paramstack ())
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
	   (setf (bintype-instantiator bintype) #',(format-symbol (symbol-package type-name) "MAKE-~A" type-name)
                 (bintype-paver bintype) ,(output-paver-lambda type-name toplevels total-length)))))))

(defun export-bintype-accessors (bintype)
  (let ((bintype-name (bintype-name bintype)))
    (export (list* bintype-name
		   (iter (for toplevel in (bintype-toplevels bintype))
			 (collect (format-symbol (symbol-package bintype-name) "~A-~A" bintype-name (apply-toplevel-op 'name toplevel))))))))
