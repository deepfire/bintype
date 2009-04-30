;;; -*- Mode: LISP; Syntax: COMMON-LISP; Package: BINTYPE; Base: 10 -*-
;;;
;;;  (c) copyright 2007-2008 by
;;;           Samium Gromoff (_deepfire@feelingofgreen.ru)
;;;
;;; This library is free software; you can redistribute it and/or
;;; modify it under the terms of the GNU Library General Public
;;; License as published by the Free Software Foundation; either
;;; version 2 of the License, or (at your option) any later version.
;;;
;;; This library is distributed in the hope that it will be useful,
;;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;;; Library General Public License for more details.
;;;
;;; You should have received a copy of the GNU Library General Public
;;; License along with this library; if not, write to the
;;; Free Software Foundation, Inc., 59 Temple Place - Suite 330,
;;; Boston, MA  02111-1307  USA.

(in-package :bintype)

(defvar *bintypes* (make-hash-table))

(defclass btobj ()
  ((offset :accessor offset :initarg :offset :documentation "offset in bits from stream begin")
   (parent :accessor parent :initarg :parent)
   (params :accessor params :initarg :params)
   (typespec :accessor typespec :initarg :typespec)
   (sub-id :accessor sub-id :initarg :sub-id)
   (width :accessor width :initarg :width)
   (interpreter-fn :accessor interpreter-fn :initarg :interpreter-fn)
   (initial-value :accessor initial-value :initarg :initial-value :initform nil)
   (final-value :accessor final-value :initarg :final-value))
  (:default-initargs
   :interpreter-fn #'values))

(defclass btcontainer (btobj)
  ((paved-p :accessor paved-p :initform nil)
   (paving-p :accessor paving-p :initform nil)
   (childs :accessor childs :initarg :childs)))

(defclass btordered (btcontainer)
  ((element-type :accessor btordered-element-type :initarg :element-type)))

(defclass btfuncstride (btordered)
  ((stride-fn :accessor btfuncstride-stride-fn :initarg :stride-fn)))

(defclass btorderedpack (btordered)
  ((length-guess :accessor btorderedpack-length-guess :initarg :length-guess)))

(defclass btstructured (btcontainer)
  ((bintype :accessor btstructured-bintype :initarg :bintype)))

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
	  (when (slot-boundp o 'childs) (length (childs o))) (btordered-element-type o)))

(defmethod print-object ((o btstructured) s)
  (format s "#<BTSTRUCTURED sub-id: ~S offset: ~X bintype: ~S>"
	  (slot-value-for-print o 'sub-id) (slot-value-for-print o 'offset)
	  (bintype-name (btstructured-bintype o))))

(defmethod print-object ((o btleaf) s)
  (format s "#<BTLEAF sub-id: ~S offset: ~X>"
	  (slot-value-for-print o 'sub-id) (slot-value-for-print o 'offset)))

(defmethod initialize-instance :after ((obj btobj) &rest rest)
  (declare (ignore rest))
  (when (slot-boundp obj 'parent)
    (setf (cref (parent obj) (sub-id obj)) obj)))

(defmethod initialize-instance :after ((obj btfuncstride) &key dimension &allow-other-keys)
  (setf (slot-value obj 'childs) (make-array dimension :initial-element nil)))

(defmethod initialize-instance :after ((obj btorderedpack) &rest rest)
  (declare (ignore rest))
  (setf (slot-value obj 'childs) (make-array (slot-value obj 'length-guess) :initial-element nil :adjustable t :fill-pointer 0)))

(defmethod initialize-instance :after ((obj btstructured) &key runtime-slot-count &allow-other-keys)
  (setf (slot-value obj 'childs) (make-array runtime-slot-count :initial-element nil :adjustable t)))

(defstruct bintype
  (name nil :type symbol)
  prefix
  (documentation nil :type (or null string))
  lambda-list
  instantiator
  paver
  slot-map	;; the first (length producing-toplevels) elements are the producing ones (plus, btbitfields...)
  setter-map	;; the map for the producing elements
  toplevels)

(define-condition bintype-condition (condition) ((bintype :accessor bintype-condition-bintype :initarg :bintype)))
(define-condition bintype-error (bintype-condition error) ())
(define-condition bintype-parse-error (bintype-error) ())
(define-condition bintype-spec-error (bintype-error) ())
(define-condition bintype-simple-error (bintype-error simple-error) ())
(define-condition bintype-simple-parse-error (bintype-parse-error bintype-simple-error) ())
(define-condition bintype-simple-spec-error (bintype-spec-error bintype-simple-error) ())

(defun bintype (name)
  (or (gethash name *bintypes*) (error 'bintype-simple-error
                                 :format-control "Unable to find the requested bintype ~S."
                                 :format-arguments (list name))))

(defun toplevel-lambda-var (toplevel var)
  (lambda-list-1 (toplevel-op-lambda-list (car toplevel)) (rest toplevel) var))

(defun slot-number (bintype slot-name)
  (position slot-name (bintype-slot-map bintype) :test #'eq))

(defgeneric cref (container sel)
  (:documentation "Reach for a child of a BTCONTAINER.")
  (:method ((btcontainer btordered) (sel integer))
    (aref (childs btcontainer) sel))
  (:method ((btcontainer btstructured) (sel symbol))
    (if-let ((slot-number (slot-number (btstructured-bintype btcontainer) sel)))
	    (aref (childs btcontainer) slot-number)
	    (error 'bintype-simple-spec-error
             :bintype (btstructured-bintype btcontainer)
             :format-control "BTSTRUCTURED ~S has no field called ~S."
             :format-arguments (list btcontainer sel)))))

(defgeneric (setf cref) (val container sel)
  (:documentation "Set a child of a BTCONTAINER.")
  (:method (val (btcontainer btordered) (sel integer))
    (setf (aref (childs btcontainer) sel) val))
  (:method (val (btcontainer btstructured) (sel symbol))
    (if-let ((slot-number (slot-number (btstructured-bintype btcontainer) sel)))
	    (setf (aref (childs btcontainer) slot-number) val)
	    (error 'bintype-simple-spec-error
             :bintype (btstructured-bintype btcontainer)
             :format-control "BTSTRUCTURED ~S has no field called ~S."
             :cormat-arguments (list btcontainer sel)))))

(defun read-bits (obj width &aux (offset (offset obj)) (bytespan (1+ (ash (+ width (logand offset #x7)) -3))))
  "Buggy. Try undefine 64bit stuff and see the world go down.."
  (declare (special *u-reader* *sequence*))
  (ldb (byte width (logand offset #x7)) (funcall *u-reader* *sequence* (ash offset -3) bytespan)))

(defun generic-u8-reader (obj)
  (declare (special *sequence*))
  (elt *sequence* (ash (offset obj) -3)))

(defun generic-u16-reader (obj)
  (declare (special *u16-reader* *sequence*))
  (funcall *u16-reader* *sequence* (ash (offset obj) -3)))

(defun generic-u32-reader (obj)
  (declare (special *u32-reader* *sequence*))
  (funcall *u32-reader* *sequence* (ash (offset obj) -3)))

(defun generic-u64-reader (obj)
  (declare (special *u64-reader* *sequence*))
  (funcall *u64-reader* *sequence* (ash (offset obj) -3)))

(defun generic-s8-reader (obj)
  (declare (special *sequence*))
  (let ((val (elt *sequence* (ash (offset obj) -3))))
    (if (logbitp 7 val)
        (- val #x100)
        val)))

(defun generic-s16-reader (obj)
  (declare (special *u16-reader* *sequence*))
  (let ((val (funcall *u16-reader* *sequence* (ash (offset obj) -3))))
    (if (logbitp 15 val)
        (- val #x10000)
        val)))

(defun generic-s32-reader (obj)
  (declare (special *u32-reader* *sequence*))
  (let ((val (funcall *u32-reader* *sequence* (ash (offset obj) -3))))
    (if (logbitp 31 val)
        (- val #x100000000)
        val)))

(defun generic-s64-reader (obj)
  (declare (special *u64-reader* *sequence*))
  (let ((val (funcall *u64-reader* *sequence* (ash (offset obj) -3))))
    (if (logbitp 63 val)
        (- val #x10000000000000000)
        val)))

(defparameter *primitive-types* (make-hash-table :test #'eq))

(defun primitive-type-p (type)
  (op-parameter-destructurer (op nil) type
    (gethash op *primitive-types*)))

(defmacro define-lambda-mapper (domain)
  (let* ((package (symbol-package domain))
         (lambda-table (format-symbol package "*~A-LAMBDA-LISTS*" domain)))
    `(progn
       (eval-when (:compile-toplevel :load-toplevel)
	 (defparameter ,lambda-table (make-hash-table :test #'eq)))
       (defun ,(format-symbol package "~A-LAMBDA-LIST" domain) (set-name)
         (gethash set-name ,lambda-table))
       (defun ,(format-symbol package "APPLY-~A" domain) (query-name form)
         (op-parameter-destructurer (set-name params) form
           (apply (format-symbol (find-package ',(package-name package)) "~A-~A-~A" ',domain set-name query-name)
                  params))))))

(defmacro define-lambda-map (domain name lambda-list &body definitions)
  (let* ((package (symbol-package domain))
         (lambda-table (format-symbol package "*~A-LAMBDA-LISTS*" domain))
         (lambda-binds (lambda-list-binds lambda-list)))
    (unless (boundp lambda-table)
      (error "~@<undefined lambda mapper ~S~@:>" domain))
    `(eval-when (:compile-toplevel :load-toplevel :execute)
       (setf (gethash ',name ,lambda-table) ',lambda-list)
       ,@(iter (for (query-name interested-by-list . body) in definitions)
               (unless (every (rcurry #'member lambda-binds) interested-by-list)
                 (error "~@<the interested-by binding specification ~S is not a subset of the main binding list ~S~@:>"
                        interested-by-list lambda-list))
               (collect
                (emit-defun (format-symbol package "~A-~A-~A" domain name query-name) lambda-list body
                 :declarations (emit-declarations :ignore (set-difference lambda-binds interested-by-list))))))))

(defmacro define-primitive-type (name lambda-list &body body)
  `(progn
     (when (primitive-type-p ',name)
       (warn "redefining ~S in DEFINE-PRIMITIVE-TYPE" ',name))
     (setf (gethash ',name *primitive-types*) t)
     ,@(when-let ((functions (remove 'defun body :key #'car :test-not #'eq)))
                 `((define-lambda-map typespec ,name ,lambda-list
                     ,@(mapcar #'rest functions))))))

(define-lambda-mapper typespec)

(defun typespec-types-match-p (typeset typespec)
  (op-parameter-destructurer (nil params) typespec
    (lambda-list-application-types-match-p (apply-typespec typeset typespec) params)))

(defun custom-map-lambda-list (fn lambda-list application &key insert-keywords)
  (map-lambda-list (lambda (type name default actual)
                     (funcall fn (if (eq type '&mandatory) name default) actual))
                   lambda-list application :insert-keywords insert-keywords))

(defun lambda-list-application-types-match-p (typespec list)
  (every #'identity (custom-map-lambda-list (order typep 1 0) typespec list)))

;; Note: the only user of 'custom processing' is the non-working typecase.
(defun typestack (typespec)
  "Obtain the whole type invocation stack for TYPESPEC."
  (op-parameter-destructurer (nil params) typespec
    (multiple-value-bind (rest-of-typestack custom-processing) (apply-typespec 'child-typestack typespec)
      (if custom-processing
          (values rest-of-typestack t)
          (cons (when params (list* 'list (custom-map-lambda-list #'quote-when (apply-typespec 'quotation typespec) params :insert-keywords t))) rest-of-typestack)))))

(defun runtime-typestack (typespec)
  (op-parameter-destructurer (nil params) typespec
    (cons params (apply-typespec 'runtime-type-paramstack typespec))))

(define-primitive-type unsigned-byte (width)
  (defun apply-safe-parameter-types () '((integer 0)))
  (defun constant-width (width) width)
  (defun child-typestack ())
  (defun runtime-type-paramstack ())
  (defun initargs (width)
    (list 'btleaf
     :value-fn (case width
                 (8 #'generic-u8-reader)
                 (16 #'generic-u16-reader)
                 (32 #'generic-u32-reader)
                 (64 #'generic-u64-reader)
                 (t (lambda (obj) (read-bits obj width))))
     :width width))
  (defun cl-type (width) `(unsigned-byte ,width))
  (defun quotation () '(nil)))

(define-primitive-type signed-byte (width)
  (defun apply-safe-parameter-types () '(integer))
  (defun constant-width (width) width)
  (defun child-typestack ())
  (defun runtime-type-paramstack ())
  (defun initargs (width)
    (list 'btleaf
     :value-fn (case width
                 (8 #'generic-s8-reader)
                 (16 #'generic-s16-reader)
                 (32 #'generic-s32-reader)
                 (64 #'generic-s64-reader)
                 (t (lambda (obj &aux (val (read-bits obj width)))
                      (if (logbitp (1- width) val) (- val (ash 1 width)) val))))
     :width width))
  (defun cl-type (width)
    `(signed-byte ,width))
  (defun quotation ()
    '(nil)))

(define-primitive-type pure (typespec expression)
  (defun apply-safe-parameter-types () '(t t))
  (defun constant-width () 0)
  (defun child-typestack ())
  (defun runtime-type-paramstack ())
  (defun initargs (expression)
    (list 'btleaf :value-fn (constantly expression) :width 0))
  (defun cl-type (typespec)
    (apply-typespec 'cl-type typespec))
  (defun quotation ()
    '(t nil)))

(define-condition displacement-out-of-range (bintype-parse-error)
  ((offset :accessor condition-offset :initarg :offset)
   (length :accessor condition-length :initarg :length)
   (misfit :accessor condition-misfit :initarg :misfit)
   (obj :accessor condition-obj :initarg :obj))
  (:report
   (lambda (cond stream)
     (format stream "~@<~S: displaced vector of length ~S at byte offset ~S doesn't fit the underlying sequence by ~S elements~:@>"
             (condition-obj cond) (condition-length cond) (condition-offset cond) (- (condition-length cond) (condition-misfit cond))))))

(defun stream-format (format-string &rest rest)
  (lambda (stream)
    (apply #'format stream format-string rest)))

(defun consume-displaced-u8-vector (dimension obj)
  (declare (special *sequence*))
  (unless (typep *sequence* '(vector (unsigned-byte 8)))
    (error 'bintype-simple-parse-error
           :format-control "underlying sequence type ~S is not subtype of (vector (unsigned-byte 8)), as required by displaced-u8-vector"
           :format-arguments (list (type-of *sequence*))))
  (let ((misfit (- (+ (ash (offset obj) -3) dimension) (array-dimension *sequence* 0))))
    (restart-case (when (plusp misfit)
                    (error 'displacement-out-of-range :obj obj :length dimension :offset (ash (offset obj) -3) :misfit misfit))
      (trim (cond)
       :report "Trim the displaced vector to fit."
       (declare (ignore cond))
       (decf dimension misfit))))
  (make-array dimension :element-type '(unsigned-byte 8) :displaced-to *sequence* :displaced-index-offset (ash (offset obj) -3)))

(define-primitive-type displaced-u8-vector (length)
  (defun apply-safe-parameter-types () '((integer 0)))
  (defun constant-width (length) (ash length 3))
  (defun child-typestack ())
  (defun runtime-type-paramstack ())
  (defun initargs (length)
    (list 'btleaf :value-fn (curry #'consume-displaced-u8-vector length) :width (ash length 3)))
  (defun cl-type ()
    `(vector (unsigned-byte 8)))
  (defun quotation ()
    '(nil)))
  
(define-primitive-type current-offset (width)
  (defun apply-safe-parameter-types () '((integer 0)))
  (defun constant-width () 0)
  (defun child-typestack ())
  (defun runtime-type-paramstack ())
  (defun initargs ()
    (list 'btleaf :value-fn #'(lambda (obj) (ash (offset obj) -3)) :width 0))
  (defun cl-type (width)
    `(unsigned-byte ,width))
  (defun quotation ()
    '(nil)))

(defun consume-zero-terminated-string (dimension obj &aux (offset (ash (offset obj) -3)))
  (declare (special *sequence*))
  (let ((search-stop (min (+ offset dimension) (length *sequence*))))
    (coerce (iter (for i from offset below (or (position 0 *sequence* :start offset :end search-stop) search-stop))
		  (collect (code-char (elt *sequence* i))))
	    'string)))
  
(define-primitive-type zero-terminated-string (dimension)
  (defun apply-safe-parameter-types () '((integer 0)))
  (defun constant-width (dimension) (ash dimension 3))
  (defun child-typestack ())
  (defun runtime-type-paramstack ())
  (defun initargs (dimension)
    (list 'btleaf :value-fn (curry #'consume-zero-terminated-string dimension) :width (ash dimension 3)))
  (defun cl-type ()
    'string)
  (defun quotation ()
    '(nil)))

(define-primitive-type zero-terminated-symbol (dimension &optional (package :keyword))
  (defun apply-safe-parameter-types () '((integer 0) &optional t))
  (defun constant-width (dimension) (ash dimension 3))
  (defun child-typestack ())
  (defun runtime-type-paramstack ())
  (defun initargs (dimension package)
    (list 'btleaf :value-fn (compose (the function (rcurry #'intern package)) #'string-upcase (the function (curry #'consume-zero-terminated-string dimension)))
                  :width (ash dimension 3)))
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
      (* constant-stride dimension 8)))
  (defun child-typestack (element-type) (typestack element-type))
  (defun runtime-type-paramstack (element-type) (runtime-typestack element-type))
  (defun initargs (dimension element-type stride stride-fn)
    (unless (primitive-type-p element-type)
      (error 'bintype-simple-spec-error
             :format-control "unknown sequence element type ~S."
             :format-arguments (list element-type)))
    (let ((stride-fn (or stride-fn (when stride (constantly stride))
                         (when-let ((stride (and (typespec-types-match-p 'apply-safe-parameter-types element-type)
                                                 (apply-typespec 'constant-width element-type))))
                           (constantly stride))
                         (error 'bintype-simple-spec-error
                                :format-control "stride is neither specified directly, nor via stride-fn, nor it is deducible from element type."
                                :format-arguments nil))))
      (list 'btfuncstride
            :element-type element-type :dimension dimension :stride-fn stride-fn
            :width (iter (for i below dimension)
                         (summing (funcall stride-fn i))))))
  (defun cl-type (element-type format)
    (ecase format
      (:list 'list)
      (:simple-vector 'simple-vector)
      (:vector `(vector ,(apply-typespec 'cl-type element-type)))))
  (defun quotation ()
    '(nil &key (element-type t) stride stride-fn format)))

(define-primitive-type orderedpack (stream-size &key element-type (length-guess 16) (format :list))
  (defun apply-safe-parameter-types () '((integer 0) &key (element-type t) (format t)))
  (defun constant-width (stream-size) (ash stream-size 3))
  (defun child-typestack (element-type) (typestack element-type))
  (defun runtime-type-paramstack (element-type) (runtime-typestack element-type))
  (defun initargs (stream-size element-type length-guess)
    (declare (optimize (debug 3)))
    (unless (primitive-type-p element-type)
      (error 'bintype-simple-spec-error
             :format-control "unknown sequence element type ~S."
             :format-arguments (list element-type)))
    (format t "length guess: ~S~%" length-guess)
    (list 'btorderedpack :element-type element-type :length-guess length-guess :width (ash stream-size 3)))
  (defun cl-type (element-type format)
    (ecase format
      (:list 'list)
      (:vector `(vector ,(apply-typespec 'cl-type element-type)))))
  (defun quotation ()
    '(nil &key (element-type t) length-guess format)))

;;; Warning: DISPATCH-VALUE is the only known instance of double evaluation. Not easy to get rid of.
(define-primitive-type typecase (dispatch-value &rest types)
  (defun apply-safe-parameter-types () '(t &rest t))
  (defun constant-width () nil)
  (defun child-typestack (dispatch-value types)
    (values (list (once-only (dispatch-value)
                    `(case ,dispatch-value
                       ,@(iter (for (signature type) in types)
                               (collect `(,signature (list ',type ,@(apply-typespec 'child-typestack type)))))
                       (t (error 'bintype-simple-parse-error
                                 :format-control "no type for dispatch value ~S"
                                 :format-arguments (list ,dispatch-value))))))
            :process-me-specially-please))
  (defun runtime-type-paramstack () (error 'bintype-simple-error :format-control "Broken." :format-arguments nil))
  (defun cl-type (types)
    `(or ,@(mapcar (compose (curry #'apply-typespec 'cl-type) #'second) types)))
  (defun quotation ()
    `(&rest nil))
  (defun initargs (types)
    (apply-typespec 'initargs (rest types))))

(defun btstructured-constant-width (type-name)
  (let ((typespecs (mapcar (curry #'apply-toplevel-op 'typespec) (bintype-toplevels (bintype type-name)))))
    (when (every (curry #'typespec-types-match-p 'apply-safe-parameter-types) typespecs)
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
    (let ((*self* obj) (bintype (btstructured-bintype obj)))
      (declare (special *self* *sequence*))
      (setf (width obj)
            (- (funcall (apply (bintype-paver bintype) (first (params obj))) (offset obj)) (offset obj)))))
  (:method ((obj btordered))
    (map 'vector #'pave (slot-value obj 'childs)))
;;   (:method ((obj btorderedpack))
;;     (flet ((pave-btorderedpack (obj stream-size &key element-type (format :list))
;;              (declare (ignore format))
;;              (op-parameter-destructurer (op params) element-type
;;                (declare (ignore params))
;;                (let ((initargs (apply-typespec 'initargs (cons op (second (params obj)))))
;;                      (offset 0))
;;                  (iter (while (< offset space-left))
;;                        (for offset initially (offset obj) then (+ offset (funcall (btfuncstride-stride-fn obj) i)))
;;                        (apply #'make-instance (first initargs) :typespec element-type :offset offset :parent obj :sub-id i :params (rest (params obj))
;;                               (rest initargs)))))))
;;       (prog1
;;           (apply #'pave-btfuncstride obj (first (params obj)))
;;         (call-next-method))))
  (:method ((obj btfuncstride))
    (flet ((pave-btfuncstride (obj dimension &key element-type stride stride-fn (format :list))
             (declare (ignore stride stride-fn format))
             (op-parameter-destructurer (op nil) element-type
               (let ((initargs (apply-typespec 'initargs (cons op (second (params obj))))))
                 (iter (for i below dimension)
                       (for offset initially (offset obj) then (+ offset (funcall (btfuncstride-stride-fn obj) i)))
                       (apply #'make-instance (first initargs) :typespec element-type :offset offset :parent obj :sub-id i :params (rest (params obj))
                              (rest initargs))
                       (finally (return offset)))))))
      (prog1
          (apply #'pave-btfuncstride obj (first (params obj)))
        (call-next-method)))))

(define-lambda-mapper toplevel-op)

(defun toplevel-types-match-p (typeset toplevel)
  (op-parameter-destructurer (nil params) toplevel
    (lambda-list-application-types-match-p (apply-toplevel-op typeset toplevel) params)))

(defun process-field (obj immediate-p stream-offset out-of-stream-offset)
  (when (typep obj 'btcontainer) 
    (pave obj))
  (when immediate-p
    (fill-value obj))
  (values (+ stream-offset (if out-of-stream-offset 0 (width obj)))
          obj))

;; circularity: emit-toplevel-pavement -> toplevel-op indirect -> e-t-p.
(defun emit-toplevel-pavement (bintype-name toplevel)
  (let ((name (toplevel-lambda-var toplevel 'name))
        (oos (toplevel-lambda-var toplevel 'out-of-stream-offset))
        (typespec (apply-toplevel-op 'typespec toplevel)))
    (with-gensyms (start-offset o-o-s-offset pretypestack subtype typestack initargs field-obj)
      (with-named-lambda-emission ((format-symbol nil "~A-~A-PAVEMENT" bintype-name name) (list start-offset)
                                   :declarations (emit-declarations :special '(*self*)))
        (multiple-value-bind (the-typestack custom-initargs-p) (typestack typespec)
          `(let* (,@(when oos `((,o-o-s-offset ,oos))) (,pretypestack (list ,@the-typestack))
                    (,subtype ,(if custom-initargs-p `(op-parameter-destructurer (type nil) (first ,pretypestack) type) `',(first typespec)))
                    (,typestack ,(if custom-initargs-p `(op-parameter-destructurer (nil params) (first ,pretypestack) (list params)) pretypestack))
                    (,initargs (apply-typespec 'initargs (cons ,subtype (first ,typestack))))
                    (,field-obj (apply #'make-instance (first ,initargs) :offset ,(if oos `(or ,o-o-s-offset ,start-offset) start-offset) :parent *self* :sub-id ',name
                                       :typespec ',typespec :params ,typestack
                                       ,@(when-let ((i-t-f-f (apply-toplevel-op 'interpreter-xform toplevel)))
                                                   `(:interpreter-fn ,i-t-f-f)) (rest ,initargs))))
             (process-field ,field-obj ,(apply-toplevel-op 'immediate-eval toplevel) ,start-offset ,(when oos o-o-s-offset))))))))

(defun set-endianness (val)
  (declare (type (member :little-endian :big-endian) val) (special *endianness-setter*))
  (funcall *endianness-setter* val))

(defun output-paver-lambda (name lambda-list toplevels)
  (with-named-lambda-emission ((format-symbol nil "PAVE-~A" name) lambda-list
                               :declarations (emit-declarations :special '(*sequence*)))
    `(compose ,@(mapcar (curry #'emit-toplevel-pavement name) (reverse toplevels)))))

(define-lambda-map toplevel-op value (name typespec &key ignore out-of-stream-offset doc)
  (typespec (typespec)                  typespec)
  (cl-type-for-field (typespec)         `(or null ,(apply-typespec 'cl-type typespec)))
  (quotation ()                         '(t t &rest nil))
  (immediate-eval ()                    nil)
  (interpreter-xform ()                 '#'values))

(define-lambda-map toplevel-op flag (name &key ignore out-of-stream-offset doc)
  (typespec ()                          '(unsigned-byte 1))
  (cl-type-for-field ()                 'boolean)
  (quotation ()                         '(t &rest nil))
  (immediate-eval ()                    nil)
  (interpreter-xform ()                 (emit-lambda '(val obj) (list (list 'plusp 'val))
                                                     :declarations (emit-declarations :ignore '(obj)))))

(defun case-able (obj)
  (typep obj '(or number symbol)))

(defun emit-match-cond/case (testform matchforms)
  (if (every (compose #'case-able #'car) matchforms)
      `(case ,testform
	 ,@matchforms
	 (t (error 'bintype-simple-parse-error
                   :format-control "Value ~S didn't match any of ~S."
                   :format-arguments (list ,testform ',matchforms))))
      (once-only (testform)
	`(cond ,@(iter (for (testval . forms) in matchforms)
		       (collect `((null (mismatch ,testform ',testval)) ,@(or forms (list nil)))))
	       (t (error 'bintype-simple-parse-error
                         :format-control "Value ~S didn't match any of ~S."
                         :format-arguments (list ,testform ',(mapcar #'car matchforms))))))))

(define-lambda-map toplevel-op match (name typespec values &key ignore out-of-stream-offset doc)
  (typespec (typespec)                  typespec)
  (cl-type-for-field ()                 t) ;; try to calculate the most specific common type of values
  (quotation ()                         '(t t t &rest nil))
  (immediate-eval (values)              t)
  (interpreter-xform (values)           (emit-lambda '(val obj) (list (emit-match-cond/case 'val values))
                                                     :declarations (emit-declarations :ignore '(obj)))))

(define-lambda-map toplevel-op indirect (name direct-typespec result-toplevel &key ignore out-of-stream-offset final-value doc)
  (typespec (direct-typespec result-toplevel final-value)
	    					(if final-value
						    (apply-toplevel-op 'typespec result-toplevel)
						    direct-typespec))
  (cl-type-for-field (result-toplevel)  (apply-toplevel-op 'cl-type-for-field result-toplevel))
  (quotation ()                         '(t t t &rest nil))
  (immediate-eval (result-toplevel)     (apply-toplevel-op 'immediate-eval result-toplevel))
  (interpreter-xform (result-toplevel)  `(compose ,(apply-toplevel-op 'interpreter-xform result-toplevel)
                                                  ,(emit-lambda `(*direct-value* obj &aux (*self* (parent obj)))
                                                                `((fill-value (nth-value 1 (funcall ,(emit-toplevel-pavement nil result-toplevel) (offset obj)))))
                                                                :declarations (emit-declarations :special `(*self* *direct-value*))))))

#| Fact: during fill-value, only leaves need offset, which is of little wonder. |#
(defgeneric fill-value (btobject)
  (:method ((obj btobj))
    (setf (final-value obj) (funcall (interpreter-fn obj) (initial-value obj) obj)))
  (:method ((obj btleaf))
    (setf (initial-value obj) (funcall (btleaf-value-fn obj) obj))
    (call-next-method))
  (:method ((obj btordered))
    (setf (initial-value obj) (map (apply-typespec 'cl-type (typespec obj)) #'fill-value (childs obj)))
    (call-next-method))
  (:method ((obj btstructured))
    (let ((bintype (btstructured-bintype obj)))
      (setf (initial-value obj) (funcall (bintype-instantiator bintype)))
      (map 'vector (lambda (fn subobj)
                     (funcall fn (fill-value subobj) (initial-value obj)))
	   (bintype-setter-map bintype) (childs obj)))
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
			   (error 'bintype-simple-spec-error
                                  :format-control "no parent of type ~S for ~S"
                                  :format-arguments (list type-name base)))
			  (t
			   (iterate (parent current))))))
    (unless (slot-boundp base 'parent)
      (error 'bintype-simple-spec-error :format-control "no parent of type ~S for ~S" :format-arguments (list type-name base)))
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

(defun parse (typespec sequence &key (endianness :little-endian) (offset 0) (error-p t) &aux *u-reader* *u16-reader* *u32-reader* *u64-reader*)
  "Parse *SEQUENCE* according to the TYPESPEC, ENDIANNESS and OFFSET, returning parsed structure. 
   ERROR-P controls whether parse errors result in conditions of BINTYPE-PARSE-ERROR subtype being signalled.
   Note that errors of BINTYPE-SPEC-ERROR subtype are signalled regardless of ERROR-P."
  (declare (special *u-reader* *u16-reader* *u32-reader* *u64-reader*))
  (let ((*sequence* (coerce-to-sequence sequence))
        (*endianness-setter* (lambda (val)
			       (setf (values *u-reader* *u16-reader* *u32-reader* *u64-reader*)
				     (ecase val
				       (:little-endian (values #'u8-seq-wordle #'u8-seq-word16le #'u8-seq-word32le #'u8-seq-word64le))
				       (:big-endian (values #'u8-seq-wordbe #'u8-seq-word16be #'u8-seq-word32be #'u8-seq-word64be)))))))
    (declare (special *sequence* *endianness-setter*))
    (funcall *endianness-setter* endianness)
    (op-parameter-destructurer (op nil) typespec
      (handler-bind ((bintype-parse-error (lambda (c) (declare (ignore c)) (unless error-p (return-from parse)))))
          (let* ((typestack (runtime-typestack typespec))
                 (initargs (apply-typespec 'initargs (cons op (first typestack))))
                 (obj (apply #'make-instance (first initargs) :offset (ash offset 3) :typespec typespec :params typestack (rest initargs))))
            (pave obj)
            (fill-value obj))))))

(defun generic-slot-accessor-name (package prefix slot-name)
  (format-symbol package "~A~A" prefix slot-name))

(defmacro defbintype (type-name lambda-list &body f &aux
                      (custom-prefix (cadr (assoc :prefix f)))
                      (prefix (if custom-prefix 
                                  (write-to-string custom-prefix :escape nil)
                                  (format nil "~A-" type-name))))
  (flet ((output-defclass-field (toplevel)
           (let ((slot-name (toplevel-lambda-var toplevel 'name))
                 (doc (toplevel-lambda-var toplevel 'doc)))
            `(,slot-name :accessor ,(generic-slot-accessor-name (symbol-package type-name) prefix slot-name)
                         :initform nil :type ,(apply-toplevel-op 'cl-type-for-field toplevel)
                         ,@(when doc `(:documentation ,doc)))))
         ;; No documentation for DEFSTRUCT slots...
         (output-defstruct-field (toplevel)
	   `(,(toplevel-lambda-var toplevel 'name) nil :type ,(apply-toplevel-op 'cl-type-for-field toplevel)))
	 (more-emitting-p (top-x top-y)
	   (and (null (toplevel-lambda-var top-x 'ignore)) (toplevel-lambda-var top-y 'ignore))))
    (let* ((documentation (cadr (assoc :documentation f)))
	   (type (or (cadr (assoc :type f)) :class))
	   (toplevels (cdr (assoc :fields f)))
	   (emission-ordered-toplevels (sort (copy-list toplevels) #'more-emitting-p))
	   (field-count (count-if-not (rcurry #'toplevel-lambda-var 'ignore) emission-ordered-toplevels))
	   (producing-toplevels (subseq emission-ordered-toplevels 0 field-count))
           (field-names (mapcar (compose (the function (rcurry #'toplevel-lambda-var 'name))) emission-ordered-toplevels)))
      (declare (type (member :class :structure) type))
      `(progn
	 ,@(case type
                 (:class `((defclass ,type-name () ,(mapcar #'output-defclass-field producing-toplevels))))
                 (:structure `((defstruct (,type-name ,@(when custom-prefix `((:conc-name ,custom-prefix))))
                                 ,@(mapcar #'output-defstruct-field producing-toplevels)))))
         (let ((field-names ',field-names))
	  (setf (gethash ',type-name *bintypes*)
		(make-bintype :name ',type-name :documentation ,documentation :lambda-list ',lambda-list :toplevels ',toplevels
			      :slot-map (make-array ,(length toplevels) :initial-contents field-names) :prefix ',prefix
			      :setter-map
                              (make-array ,field-count
                               :initial-contents
                               (list ,@(iter (for field-name in field-names)
                                             (repeat field-count)
                                             (collect `(lambda (val o)
                                                         (setf (,(generic-slot-accessor-name (symbol-package type-name) prefix field-name) o) val)))))))))
	 (define-primitive-type ,type-name ,lambda-list
           (defun apply-safe-parameter-types () '(&rest t))
           (defun child-typestack ())
           (defun runtime-type-paramstack ())
           (defun constant-width () (btstructured-constant-width ',type-name))
	   (defun initargs ,(lambda-list-binds lambda-list) (declare (ignorable ,@(lambda-list-binds lambda-list)))
                  (list 'btstructured :bintype (bintype ',type-name) :runtime-slot-count ,(length toplevels)))
	   (defun cl-type () ',type-name)
	   (defun quotation () '(&rest nil)))
	 (let* ((bintype (bintype ',type-name)))
	   (setf (bintype-instantiator bintype) ,(case type
                                                       (:class `(curry #'make-instance ',type-name))
                                                       (:structure `#',(format-symbol (symbol-package type-name) "MAKE-~A" type-name)))
                 (bintype-paver bintype) ,(output-paver-lambda type-name lambda-list toplevels)))))))

(defun export-bintype (bintype)
  (with-slots (name prefix toplevels) bintype
    (export
     (list* name
            (iter (for toplevel in toplevels)
                  (for toplevel-name = (toplevel-lambda-var toplevel 'name))
                  (for symbol = (format-symbol (symbol-package name) "~A~A" prefix toplevel-name))
                  (collect toplevel-name)
                  (collect symbol))))))
