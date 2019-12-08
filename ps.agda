module _ where

  module ps (A : Set)
            (B : A -> Set)
            (C : (x : A)-> B x -> Set)
            (d : (x : A)-> (y : B x)-> C x y -> A) where

    data fm : A -> Set where
      intro : (x : A) -> (y : B x) -> (f : (z : C x y) -> fm (d x y z) ) -> fm x

    ex : { H : (x : A) -> (t : fm x) -> Set }->
         ( c : (x : A) -> (y : B x)-> (f : (z : C x y) → fm (d x y z)) ->
               ( (z : C x y)-> H (d x y z) (f z) ) -> H x (intro x y f)
         ) -> 
         (x : A)-> (t : fm x) -> H x t
    ex {C} c _ (intro x y f) = c x y f (λ z → ex {C} c (d x y z) (f z))

  module ps* ( A : Set ) ( A' : Set ) ( A* : A -> A' -> Set )
             ( B : A -> Set ) ( B' : A' -> Set )
             ( B* : (a : A) -> (a' : A') -> A* a a' -> B a -> B' a' -> Set )
             ( C  : (a : A)-> B a -> Set )
             ( C' : (a' : A')-> B' a' -> Set )
             ( C* : (a : A) -> (a' : A') -> (a* : A* a a') ->
                    ( b : B a) -> (b' : B' a') -> B* a a' a* b b' ->
                    C a b -> C' a' b' -> Set )
             ( d  : (a : A) -> (b : B a)-> C a b -> A)
             ( d' : (a' : A') -> (b' : B' a')-> C' a' b' -> A')
             ( d* : (a : A) -> (a' : A') -> (a* : A* a a') ->
                    (b : B a) -> (b' : B' a') -> (b* : B* a a' a* b b')->
                    (c : C a b) -> (c' : C' a' b')-> (c* : C* a a' a* b b' b* c c')->
                    A* (d a b c) (d' a' b' c'))
        where
    open ps A B C d public 
    open ps A' B' C' d' public renaming (fm to fm'; intro to intro' ; ex to ex') 

    data fm* : (a : A) -> (a' : A') -> A* a a' -> fm a -> fm' a' -> Set where
      intro* : (a : A) -> (a' : A') -> (a* : A* a a') ->
               (b : B a) -> (b' : B' a') -> (b* : B* a a' a* b b') ->
               (f : (c : C a b) -> fm (d a b c)) ->    
               (f' : (c' : C' a' b') -> fm' (d' a' b' c')) ->    
               (f* : (c : C a b) -> (c' : C' a' b') -> (c* : C* a a' a* b b' b* c c') ->
                     fm* (d a b c) (d' a' b' c') (d* a a' a* b b' b* c c' c*) (f c) (f' c')) ->
               fm* a a' a* (intro a b f) (intro' a' b' f')

    ex* : {K : (a : A)-> (a' : A') -> (a* : A* a a') -> (z : fm a) -> (z' : fm' a') -> fm* a a' a* z z' -> Set}
          (k : (a : A)-> (a' : A') -> (a* : A* a a')->
               (b : B a)->(b' : B' a')-> (b* : B* a a' a* b b')->
               (f  : (z : C a b) → fm (d a b z)) ->
               (f' : (z : C' a' b') → fm' (d' a' b' z)) ->
               (f* : (c : C a b) -> (c' : C' a' b') -> (c* : C* a a' a* b b' b* c c') ->
                     fm* (d a b c) (d' a' b' c') (d* a a' a* b b' b* c c' c*) (f c) (f' c')) ->
               (g  : (c : C a b)->(c' : C' a' b') -> (c* : C* a a' a* b b' b* c c') ->
                     K (d a b c) (d' a' b' c') (d* a a' a* b b' b* c c' c*) (f c) (f' c') (f* c c' c*)) -> 
               K a a' a* (intro a b f) (intro' a' b' f') (intro* a a' a* b b' b* f f' f*)
          )->
          (a : A)-> (a' : A') -> (a* : A* a a') -> (z : fm a) -> (z' : fm' a') -> (z* : fm* a a' a* z z') -> K a a' a* z z' z*
    ex* {K} k _ _ _ (intro' _ _ _) (intro' _ _ _) (intro* a a' a* b b' b* f f' f*)
          = k a a' a* b b' b* f f' f*
            (λ c c' c* → ex* {K} k (d a b c) (d' a' b' c') (d* a a' a* b b' b* c c' c*) (f c) (f' c') (f* c c' c*))

  module ps-in-model ( A : Set ) ( A* : A -> A -> Set )
                     ( B : A -> Set ) ( B* : (a a' : A)-> A* a a' -> B a -> B a' -> Set ) 
                     ( C  : (a : A)-> B a -> Set )
                     ( C* : (a : A) -> (a' : A) -> (a* : A* a a') ->
                            (b : B a) -> (b' : B a') → B* a a' a* b b' → C a b → C a' b' → Set)
                     ( d  : (a : A) -> (b : B a)-> C a b -> A)
                     ( d* : (a : A) -> (a' : A) -> (a* : A* a a') ->
                            (b : B a) -> (b' : B a') -> (b* : B* a a' a* b b')->
                            (c : C a b) -> (c' : C a' b')-> (c* : C* a a' a* b b' b* c c')->
                          A* (d a b c) (d a' b' c'))
    where

    open ps* A A A* B B B* C C C* d d d* public
    module _ (H : (a : A) -> (t : fm a) -> Set)
             (H* : (a a' : A) (a* : A* a a') (t : fm a) (t' : fm a') (t* : fm* a a' a* t t') ->
                   (H a t ) -> (H a' t') -> Set
             )
             ( s : (a : A) -> (b : B a)-> (f : (c : C a b) → fm (d a b c)) ->
               (g : (c : C a b)-> H (d a b c) (f c))-> H a (intro a b f) )
             ( s* : (a a' : A) (a* : A* a a')
                    (b : B a) (b' : B a') (b* : B* a a' a* b b')
                    (f : (c : C a b) → fm (d a b c))
                    (f' : (c' : C a' b') → fm' (d a' b' c'))
                    (f* : (c : C a b) (c' : C a' b') (c* : C* a a' a* b b' b* c c') →
                         fm* (d a b c) (d a' b' c') (d* a a' a* b b' b* c c' c*)
                             (f c) (f' c')) →
                    ( (c : C a b) (c' : C a' b') (c* : C* a a' a* b b' b* c c') →
                      H* (d a b c) (d a' b' c') (d* a a' a* b b' b* c c' c*)
                         (f c) (f' c') (f* c c' c*)
                         (ex {H} s (d a b c) (f c))  (ex {H} s (d a' b' c') (f' c'))
                    ) →
                      H* a a' a* (intro a b f) (intro a' b' f') (intro* a a' a* b b' b* f f' f*)
                         (s a b f (λ z → ex {H} s (d a b z) (f z)))
                         (s a' b' f' (λ z → ex {H} s (d a' b' z) (f' z)))
             )
      where
        h : (a : A) -> (t : fm a) → H a t
        h = ex {H} s
        M :  (a a' : A) (a* : A* a a') (t : fm a) (t' : fm a') (t* : fm* a a' a* t t') -> Set
        M a a' a* t t' t*   = H* a a' a* t t' t* (h a t) (h a' t')
        m : (a a' : A) (a* : A* a a')
            (b : B a) (b' : B a') (b* : B* a a' a* b b')
            (f : (c : C a b) → fm (d a b c))
            (f' : (c' : C a' b') → fm' (d a' b' c'))
            (f* : (c : C a b) (c' : C a' b')
                  (c* : C* a a' a* b b' b* c c') →
                 fm* (d a b c) (d a' b' c') (d* a a' a* b b' b* c c' c*)
                     (f c) (f' c')
            ) →
            ( (c : C a b) (c' : C a' b') (c* : C* a a' a* b b' b* c c') ->
              M (d a b c) (d a' b' c') (d* a a' a* b b' b* c c' c*) (f c) (f' c') (f* c c' c*)
            ) →
              M a a' a* (intro a b f) (intro a' b' f') (intro* a a' a* b b' b* f f' f*)
        m = s*
        h* : (x x' : A) (x* : A* x x') (t : fm x ) (t' : fm' x') (t* : fm* x x' x* t t') -> M x x' x* t t' t*
        h* = ex* {M} m
    
