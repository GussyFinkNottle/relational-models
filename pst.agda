module _ where

  module ps (A : Set)
            (B : A -> Set)
            (C : (x : A)-> B x -> Set)
            (d : (x : A)-> (y : B x)-> C x y -> A) where

    data fm : A -> Set where
      intro : (x : A) -> (y : B x) -> (f : (z : C x y) -> fm (d x y z) ) -> fm x

    ex : { H : (x : A) -> (t : fm x) -> Set }->
         ( c : (x : A) -> (y : B x)-> (f : (z : C x y) → fm (d x y z)) ->
               (g : (z : C x y)-> H (d x y z) (f z))-> H x (intro x y f) ) -> 
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
                    ( b : B a) -> (b' : B' a') -> (b* : B* a a' a* b b')->
                    ( c : C a b) -> (c' : C' a' b')-> (c* : C* a a' a* b b' b* c c')->
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
    ex* {K} k _ _ _ (intro' _ _ _) (intro' _ _ _) (intro* a a' a* b b' b* f f' f*) = k a a' a* b b' b* f f' f*
        λ c c' c* → ex* {K} k (d a b c) (d' a' b' c') (d* a a' a* b b' b* c c' c*) (f c) (f' c') (f* c c' c*)
{-
  module w-in-model ( A : Set ) ( A* : A -> A -> Set )
                    ( B : A -> Set ) ( B* : (a a' : A)-> A* a a' -> B a -> B a' -> Set ) where
    open w* A A A* B B B* public
    module _ (C : fm -> Set)
             (C* : (z z' : fm)-> (z* : fm* z z')-> C z -> C z' -> Set)
             (c : (a : A)-> (f : B a -> fm) -> ((b : B a)-> C (f b)) -> C (intro a f))
             (c* : (a a' : A) (a* : A* a a') (f : B a → fm) (f' : B a' → fm)
                   (f* : (b : B a) (b' : B a') → B* a a' a* b b' → fm* (f b) (f' b')) →
                     ((b : B a) (b' : B a') (b* : B* a a' a* b b') →
                      C* (f b) (f' b') (f* b b' b*) (ex {C} c (f b)) (ex {C} c (f' b'))) →
                     C* (intro a f) (intro a' f') (intro* a a' a* f f' f*)
                     (c a f (λ b → ex {C} c (f b))) (c a' f' (λ b → ex {C} c (f' b)))) where
          h : (z : fm) -> C z
          h = ex {C} c
          D : (z z' : fm)-> (z* : fm* z z')-> Set
          D z z' z* = C* z z' z* (h z) (h z')
          d : (a a' : A) (a* : A* a a') (f : B a → fm) (f' : B a' → fm)
                (f* : (b : B a) (b' : B a') → B* a a' a* b b' → fm* (f b) (f' b')) →
                ((b : B a) (b' : B a') (b* : B* a a' a* b b') →
                 C* (f b) (f' b') (f* b b' b*) (h (f b)) (h (f' b'))) →
                C* (intro a f) (intro a' f') (intro* a a' a* f f' f*)
                (c a f (λ b → h (f b))) (c a' f' (λ b → h (f' b)))
          d = c*
          h* :  (z z' : fm)-> (z* : fm* z z')-> D z z' z*
          h* = ex* {D} d 

-}
