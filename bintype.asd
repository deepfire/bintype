(defpackage :bintype.system
  (:use :cl :asdf))

(in-package :bintype.system)

(defsystem :bintype
  :depends-on (:alexandria :captured-stream :semi-precious)
  :components
  ((:file "bintype")))
