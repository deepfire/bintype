(defpackage :bintype.system
  (:use :cl :asdf))

(in-package :bintype.system)

(defsystem :bintype
  :depends-on (:alexandria :pergamum)
  :components
  ((:file "bintype")))
