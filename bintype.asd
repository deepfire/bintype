;;; -*- Mode: Lisp; indent-tabs-mode: nil -*-

(defsystem :bintype
  :depends-on (:alexandria :pergamum)
  :components
  ((:file "packages")
   (:file "bintype" :depends-on ("packages"))))
