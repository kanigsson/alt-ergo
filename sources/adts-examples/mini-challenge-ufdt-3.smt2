(declare-sort e 0)

(declare-datatypes ((t 0)) (((C (hd e) (tl t)) (N))))

(declare-sort G 0)

(declare-fun f (t t) t)

(declare-fun gt0 (G) t)

(declare-fun gt1 (G) t)

(declare-const U G)

(assert
 (forall ((x G))
         (=
          (f (gt0 x) (gt1 x))
          (ite ((_ is C) (gt0 x))
               (ite ((_ is C) (gt1 x)) (C (hd (gt0 x)) (C (hd (gt1 x)) (f (tl (gt0 x)) (tl (gt1 x))))) (C (hd (gt0 x)) (tl (gt0 x)))) (gt1 x))
          )
         )
 )

(assert
 (and
  (= N (gt0 U))
  (not (= (gt1 U) (f N (gt1 U)))
       )
  )
 )

(check-sat)

