; Copyright (C) 2024 Nexus Laboratories, Inc.
;
; License: A 3-clause BSD license. See the file /3BSD-mod.txt.

; The notice below is copied from
; https://github.com/acl2/acl2/blob/master/books/kestrel/crypto/r1cs/sparse/gadgets/boolean.lisp
; on 30 July, 2024.
; Many contents in this file are copied from above and in many cases modified.

; Copyright (C) 2020-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)


(include-book "kestrel/crypto/r1cs/sparse/r1cs" :dir :system)
(include-book "kestrel/prime-fields/prime-fields-rules" :dir :system)
(include-book "kestrel/crypto/r1cs/sparse/rules" :dir :system)
(include-book "kestrel/arithmetic-light/mod" :dir :system)

(defpkg "NEXUS-EXPERIMENT"
    (append '(R1CS) *acl2-exports*))
