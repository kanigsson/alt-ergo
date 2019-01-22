(set-logic ALL)


(declare-datatypes
 ((TU 0) (TV 0))
 (((X (thexxxx Int)))
  ((Y (rep_enatxxxx Int))))
 )

;(declare-sort TU 0)
;(declare-sort TV 0)

(declare-fun v1 () TV)

(declare-fun v2 () TV)

(declare-fun t1 () Int)

(declare-fun t2 () Int)

(declare-fun f (TV Int) Int)

(declare-fun p (Int TV) Bool)

(declare-fun g (Int TV) Int)

(declare-fun h (Int TV) TV)

(assert (not (= (f v1 3) (f v1 4))))

(assert (= (f v2 3) (f v2 4)))

(assert (p (g 4 v1) v2))


(assert
 (forall ((?v0 TV) (?v1 TV) (?v2 Int))
         (= (f ?v0 (f ?v1 ?v2)) (f (h (g 4 ?v0) ?v1) ?v2))
         )
 )

(assert
 (forall ((?v0 TV) (?v1 TV))
         (=> (p (g 4 ?v0) ?v1)
             (= (h (g 4 ?v0) ?v1) ?v0))
         )
 )

(check-sat)

