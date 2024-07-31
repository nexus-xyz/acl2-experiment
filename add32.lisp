; Soundness proof of a 32-bit addition gadget in R1CS
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

(in-package "NEXUS-EXPERIMENT")

;; 2^32
(defconst *2-to-32* (expt 2 32))

;; Make an R1CS constraint (in sparse form) that asserts that a var is
;; either 0 or negative 2-to-32.  The constraint is of the form:
;; (v)(v + *2-to-32*) = 0.
(defund make-32bit-carry-constraint (var-name)
  (declare (xargs :guard (symbolp var-name)))
  (r1cs::r1cs-constraint
   (list `(1 ,var-name))               ;; a vector
   (list `(1 ,var-name) `(,*2-to-32* 1)) ;; b vector
   '()                                 ;; c vector (just zero)
   )
  )

;; make-32bit-carry-constrains gives a constraint
(defthm r1cs-constraintp-of-make-32bit-carry-constraint
  (implies (symbolp var-name)
           (r1cs::r1cs-constraintp (make-32bit-carry-constraint var-name)))
  :hints (("Goal" :in-theory (enable make-32bit-carry-constraint))))

(defun 32-bit-carryp (x p)
  (or (equal (- p *2-to-32*) x) (equal 0 x)))

;; Prove that, if we make a 32bit-carry constraint for a var, then the constraint
;; holds over a valuation (that binds the var) iff the value of the var is
;; either -2^32 or 0.
(defthm make-32bit-carry-constraint-correct
  (implies (and (dm::primep p)
                (r1cs::r1cs-valuationp valuation p)
                (r1cs::valuation-bindsp valuation var-name)
                (< *2-to-32* p)
                )
           (equal (r1cs::r1cs-constraint-holdsp (make-32bit-carry-constraint var-name) valuation p)
                  (32-bit-carryp (acl2::lookup-eq var-name valuation) p)))
  :hints (("Goal" :in-theory (e/d (make-32bit-carry-constraint
                                     r1cs::r1cs-constraint-holdsp
                                     r1cs::integerp-of-lookup-equal
                                     r1cs::acl2-numberp-of-lookup-equal)
                                  ;; distributivity gets the proof astray
                                  (pfield::mul-of-add-arg1 pfield::mul-of-add-arg2))
                  )))

;; Make another R1CS constraint (in sparse form) that asserts that
;; three variables added together is the fourth.
;; either 0 or negative 2-to-32.  The constraint is of the form:
;; (a + b + c)(1) = d.
(defund make-triple-sum-constraint
    (var-name-a var-name-b var-name-c var-name-d)
  (declare (xargs :guard (and
                          (symbolp var-name-a)
                          (symbolp var-name-b)
                          (symbolp var-name-c)
                          (symbolp var-name-d))))
  (r1cs::r1cs-constraint
   (list `(1 ,var-name-a) `(1 ,var-name-b) `(1 ,var-name-c))
   (list '(1 1))
   (list `(1 ,var-name-d))))

;; make-triple-sum-constraint gives a constraint
(defthm r1cs-constraintp-of-make-triple-sum-constraint
  (implies (and (symbolp v1) (symbolp v2) (symbolp v3) (symbolp v4))
           (r1cs::r1cs-constraintp (make-triple-sum-constraint v1 v2 v3 v4)))
  :hints (("Goal" :in-theory (enable make-triple-sum-constraint))))

;; Specification of the triple-sum constraint
(defun triple-sump (x y z s p)
  (equal
   (pfield::add x (pfield::add y z p) p) s))

;; Prove the correctness of the triple-sum constraint
(defthm make-triple-sum-constraint-correct
  (implies (and (dm::primep p)
                (r1cs::r1cs-valuationp valuation p)
                (r1cs::valuation-bindsp valuation va)
                (r1cs::valuation-bindsp valuation vb)
                (r1cs::valuation-bindsp valuation vc)
                (r1cs::valuation-bindsp valuation vd)
                )
           (equal (r1cs::r1cs-constraint-holdsp
                   (make-triple-sum-constraint va vb vc vd) valuation p)
                  (triple-sump
                   (acl2::lookup-eq va valuation)
                   (acl2::lookup-eq vb valuation)
                   (acl2::lookup-eq vc valuation)
                   (acl2::lookup-eq vd valuation) p)))
  :hints (("Goal" :in-theory (e/d (make-triple-sum-constraint
                                     r1cs::r1cs-constraint-holdsp
                                     r1cs::integerp-of-lookup-equal
                                     r1cs::acl2-numberp-of-lookup-equal)
                                  ())
                  )))

;; The specification of 32-bit addition
(defun add32p (x y z)
  (equal
   (mod (+ x y) *2-to-32*)
   z))

(local
 (include-book "centaur/bitops/floor-mod" :dir :system)
)

(local
 (defthmd floor-one
     (implies
      (and
       (integerp M)
       (integerp N)
       (< 0 M)
       (<= M N)
       (< N (* 2 M)))
      (equal (floor N M) 1))
   :hints (("Goal" :in-theory (e/d (acl2::floor-unique) (floor))))
   ))

(local
 (defthm mod-around-double
     (implies
      (and
       (integerp M)
       (integerp N)
       (< 0 M)
       (<= M N)
       (< N (* 2 M)))
      (equal
       (MOD N M)
       (- N M)
       ))
   :hints (("Goal" :in-theory (e/d (mod floor-one)
                                   (floor))))
   ))

(local
 (defthm modpp
     (implies
      (and
       (integerp p)
       (integerp x)
       (integerp z)
       (< 0 P)
       (<= 0 Z)
       )
      (equal
       (MOD (+ X P Z) P)
       (MOD (+ X Z) P)))
   ))

(local
 (defthm negative-becomes-big
     (implies
      (and
       (< 8589934592 P)
       (integerp P)
       (< (+ X Y) 4294967296)
       (INTEGERP X)
       (INTEGERP Y)
       (<= 0 X)
       (<= 0 Y))
      (equal
       (MOD (+ -4294967296 X Y) P)
       (- P (- 4294967296 (+ X Y)))))
   :hints (("Goal" :in-theory (e/d (mod) (floor))
                   :use ((
                          :instance
                          acl2::floor-of-x-negative-step
                          (X (+ -4294967296 X Y))
                          (Y P)
                          ))
                   ))
   ))

(local
 (defthm rather-small
     (implies
      (and
       (INTEGERP P)
       (< 8589934592 P)
       (< X 4294967296)
       (< Y 4294967296)
       (INTEGERP X)
       (INTEGERP Y)
       (<= 0 X)
       (<= 0 Y)
       (< (MOD (+ -4294967296 X Y) P)
          4294967296))
      (equal
       (MOD (+ X Y) 4294967296) (- (+ X Y) 4294967296)))
   :hints (("Goal"
            :cases
            ((<= 4294967296 (+ X Y)))
            ))
   ))

(local
 ;; TODO: avoid opening pfield abstraction
 (defthmd add32p-sound1
     (implies
      (and
       (dm::primep p)
       (< (* 2 *2-to-32*) p)
       (32-bit-carryp o p)
       (triple-sump x y o z p)
       (integerp x)
       (integerp y)
       (integerp z)
       (integerp o)
       (<= 0 x)
       (<= 0 y)
       (<= 0 z)
       (< x *2-to-32*)
       (< y *2-to-32*)
       (< z *2-to-32*)
       (<= 0 o)
       (< o p)
       )
      (add32p x y z))
   :hints (("Goal" :in-theory (e/d (pfield::add) (mod))))
   ))


;; Make a sequence of R1CS constraints in sparse form that asserts that three vars
;; var-x, var-y and var-z are in arelation var-x + var-y = var-z modulo
;; 2^32.

;; How do I combine circuits into a bigger circuit?
;; sounds like
;; a) make a list of constraints (r1cs-constraint-listp)
;; b) switch to pfcs

(defun make-add32-constraints (var-x var-y var-o var-z)
  (list
   (make-32bit-carry-constraint var-o)
   (make-triple-sum-constraint var-x var-y var-o var-z)))

(defthm r1cs-constraint-listp-of-make-add32-constraints
    (implies
     (and (symbolp var-x) (symbolp var-y) (symbolp var-o) (symbolp var-z))
     (r1cs::r1cs-constraint-listp (make-add32-constraints var-x var-y var-o var-z))))

;; soundness of the 32-bit addition circuit, assuming range-check elsewhere
(defthmd make-add32-constraints-sound
    (implies
     (and
      (dm::primep p)
      (< (* 2 *2-to-32*) p)
      (r1cs::r1cs-valuationp valuation p)
      (r1cs::valuation-bindsp valuation var-x)
      (r1cs::valuation-bindsp valuation var-y)
      (r1cs::valuation-bindsp valuation var-o)
      (r1cs::valuation-bindsp valuation var-z)
      (< (acl2::lookup-eq var-x valuation) *2-to-32*)
      (< (acl2::lookup-eq var-y valuation) *2-to-32*)
      (< (acl2::lookup-eq var-z valuation) *2-to-32*)
      (r1cs::r1cs-constraints-holdp
       (make-add32-constraints var-x var-y var-o var-z)
       valuation p)
      )
     (add32p
      (acl2::lookup-eq var-x valuation)
      (acl2::lookup-eq var-y valuation)
      (acl2::lookup-eq var-z valuation)
      ))
  :hints (("Goal" :in-theory (e/d
                              ()
                              (add32p))
                  :use ((:instance add32p-sound1
                                   (x (acl2::lookup-eq var-x valuation))
                                   (y (acl2::lookup-eq var-y valuation))
                                   (z (acl2::lookup-eq var-z valuation))
                                   (o (acl2::lookup-eq var-o valuation))
                                   ))
                  ))
  )
;; TODO: hide O variable, which should be hidden (using PFCS).
;; demo-idea: remove (* 2) in the size of the field.
