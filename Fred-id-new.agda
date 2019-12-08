module _ where

  rel : (A A' : Set) -> Set₁
  rel A A' = A -> A' -> Set

  module id (A : Set) where
    data fm : rel A A where
      intro : (a : A) -> fm a a

    ex : { C : (a b : A) -> fm a b -> Set }->
         ( (a : A) -> C _ _  (intro a) )->
         ( a a' : A) -> (aa' : fm a a') -> C a a' aa'
    ex {C} c a a (intro a) = c a


  module id* (A : Set) (A' : Set) (A* : rel A A') where

    open id A  public
    open id A' public renaming (fm to fm'; intro to intro'; ex to ex')

    data fm* : (a : A)->(a' : A')->(a* : A* a a')->
               (b : A)->(b' : A')->(b* : A* b b')->
               rel (fm a b) (fm' a' b') where
         intro* : (a : A)->(a' : A')->(a* : A* a a')->
                  fm* a a' a* a a' a* (intro a) (intro' a')

    ex* : {C* : (a : A)(a' : A')(a* : A* a a') ->
                (b : A)(b' : A')(b* : A* b b') ->
                (z : fm a b)(z' : fm' a' b') -> fm* a a' a* b b' b* z z' -> Set
          } ->
          (c* : (a : A) -> (a' : A') -> (a* : A* a a')-> fm a a -> fm' a' a' ->
               C* a a' a* a a' a* (intro a) (intro' a') (intro* a a' a*)
          ) ->
          (a : A) -> (a' : A') -> (a* : A* a a') ->
          (b : A) -> (b' : A') -> (b* : A* b b') ->
          (z : fm a b) -> (z' : fm' a' b') -> (z* : fm* a a' a* b b' b* z z') ->
          C* a a' a* b b' b* z z' z*
    ex* {C*} c* _ _ _ _ _ _ _ _ (intro* a a' a*)
      = c* a a' a* (intro a) (intro' a')

-- the question now: will that give us the interpretation of ex ?

  module id-in-model (A : Set) (A* : rel A A )
               where
    open id* A A A* public
    module _ (C : (a b : A)-> fm a b -> Set)
             (C* : (a a' : A) -> (a* : A* a a') -> (b b' : A)-> (b* : A* b b')->
                (z : fm a b) -> (z' : fm a' b') -> (z* : fm* a a' a* b b' b* z z') ->
                rel (C a b z) (C a' b' z')
             )
             (c : (a : A) -> C a a (intro a))
             (c* : (a a' : A)-> (a* : A* a a') ->
                   C* a a' a* a a' a* (intro a) (intro a') (intro* a a' a*) (c a) (c a')
             )
      where

      h* : (a a' : A)(a* : A* a a')
           (b b' : A)(b* : A* b b')
           (z : fm a b)(z' : fm a' b')(z* : fm* a a' a* b b' b* z z') ->
           C* a a' a* b b' b* z z' z* (ex {C} c a b z) (ex {C} c a' b' z')
      h* a a' a* b b' b* z z' z* = ex* {D} d a a' a* b b' b* z z' z*
        where
          D : (a a' : A)(a* : A* a a')
              (b b' : A) (b* : A* b b')
              (z : fm a b)(z' : fm' a' b') ->
              fm* a a' a* b b' b* z z' -> Set
          D x x' x* y y' y* u u' u*
            = C* x x' x* y y' y* u u' u* (ex {C} c x y u) (ex {C} c x' y' u')
          d : (x x' : A) (x* : A* x x') →
              fm x x → fm' x' x' →
              D x x' x* x x' x* (intro x) (intro' x') (intro* x x' x*)
          d x x' x* xx x'x' = c* x x' x*
