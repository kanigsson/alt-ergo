(declare-sort t 0)

(declare-datatypes ((dt 0) (ds 0)) (((A)) ((X))))

(declare-fun u () ds)

(declare-fun v () ds)

(declare-fun t1 () t)

(declare-fun t2 () t)

(declare-fun f (ds t) t)

(assert (not (= (f u t1) (f u t2))))

(assert (= (f v t1) (f v t2)))

(check-sat)

