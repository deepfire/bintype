(defpackage bintype
  (:use :common-lisp :alexandria :pergamum :iterate)
  (:export
   #:bintype #:define-primitive-type #:defbintype #:parse #:export-bintype
   #:bintype-condition #:bintype-error #:bintype-parse-error #:bintype-spec-error #:bintype-simple-error
   #:bintype-condition-bintype
   #:expr #:_ #:flag #:match #:plain #:indirect
   #:bcd #:pure #:current-offset #:displaced-u8-vector #:terminated-string #:terminated-symbol #:funcstride-sequence
   #:set-endianness #:offset #:parent #:sub #:value #:path-value
   #:*self* #:*sequence* #:*direct-value* #:displacement-out-of-range #:trim))
