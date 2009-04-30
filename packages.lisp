(defpackage bintype
  (:use :common-lisp :alexandria :pergamum :iterate)
  (:export
   #:bintype #:define-primitive-type #:defbintype #:parse #:export-bintype
   #:bintype-condition #:bintype-error #:bintype-parse-error #:bintype-spec-error #:bintype-simple-error
   #:bintype-simple-parse-error #:bintype-simple-spec-error #:bintype-condition-bintype
   #:expr #:_ #:flag #:match #:plain #:indirect
   #:pure #:current-offset #:displaced-u8-vector #:zero-terminated-string #:zero-terminated-symbol #:funcstride-sequence
   #:set-endianness #:offset #:parent #:sub #:value #:path-value
   #:*self* #:*sequence* #:*direct-value* #:displacement-out-of-range #:trim))
