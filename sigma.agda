module _ where 

  module sigma (A : Set) (B : A -> Set) where

    data fm : Set where                 -- formation
      mk :  (a : A) -> B a -> fm        -- introduction

    ex : { C : fm -> Set } ->           -- elimination
         ( c : (a : A) -> (b : B a) -> C (mk a b) ) ->
         ( z : fm ) -> C z
    ex c (mk a b) = c a b               -- computation

    pi0 : fm -> A
    pi0 = ex (λ a _ → a) 

    pi1 : (z : fm) -> B (pi0 z)
    pi1 = ex (λ _ b → b) 

    eta : {X : fm -> fm -> Set}->         -- pairing is Leibnitzically surjective
          ((a : fm) -> X a a) ->
          (z : fm) -> X z (mk (pi0 z) (pi1 z)) 
    eta {X} r  = ex {λ z → X z (mk (pi0 z) (pi1 z))} -- needn't be explicit
                    (λ a b → r (mk a b))

-- Extension of standard type-theory with which we interpret sigma rules.

  module sigma* (A : Set) (A' : Set)
             ( A* : A -> A' -> Set )
             ( B : A -> Set ) ( B' : A' -> Set )
             ( B* : (a : A) -> (a' : A') -> A* a a' -> B a -> B' a' -> Set )
        where
    open sigma A B public 
    open sigma A' B' public renaming (fm to fm'; mk to intro' ; ex to ex'; pi0 to pi0' ; pi1 to pi1' ; eta to eta')

    data fm* : fm -> fm' -> Set where
      intro* : (a : A) -> ( b : B a )->
               (a' : A') -> ( b' : B' a' ) ->
               (a* : A* a a') -> B* a a' a* b b' 
               -> fm* (mk a b) (intro' a' b')  

    ex* : { D : (z : fm) -> (z' : fm') -> fm* z z' -> Set }->
          ( d : (a : A)-> (b : B a) ->               -- maybe reorder d's arguments for clarity
                (a' : A') -> (b' : B' a') ->
                (a* : A* a a') -> (b* : B* a a' a* b b') ->
--                D (mk a b) (intro' a' b') (intro* a b a' b' a* b*) ) -> 
                D _ _ (intro* a b a' b' a* b*) ) -> 
          ( z : fm ) -> (z' : fm') -> (z* : fm* z z') -> D z z' z*
--    ex* {D} d (intro' a b) (intro' a' b') (intro* a b a' b' a* b*) = d a b a' b' a* b* 
    ex* {D} d _ _ (intro* a b a' b' a* b*) = d a b a' b' a* b* 

  module sigma-in-model
           (A : Set )       (A* : A -> A -> Set)
           (B : A -> Set)   (B* : (a a' : A)-> A* a a' -> B a -> B a' -> Set)
         where
    open sigma* A A A* B B B* public hiding (fm' ; intro' ; ex') 
    module _ (C : fm -> Set)
             (C* : (z z' : fm)-> (z* : fm* z z')-> C z -> C z' -> Set)   -- C, in the model
             (c : (a : A)-> (b : B a)-> C (mk a b))
             (c* : (a : A)-> (b : B a) -> (a' : A)-> (b' : B a')->                       -- c in the model (??)
                   (a* : A* a a')-> (b* : B* a a' a* b b' )->
                   C* (mk a b) (mk a' b') (intro* a b a' b' a* b*) (c a b) (c a' b')) 
          where
            h : (z : fm) -> C z
            h = ex {C} c
            D : (z z' : fm) -> fm* z z' -> Set
            D z z' z* = C* z z' z* (h z) (h z')                 -- choose right D ...
            d : ( a : A )  -> ( b : B a )  ->
                ( a' : A ) -> ( b' : B a' ) ->
                ( a* : A* a a' ) -> ( b* : B* a a' a* b b' ) ->
--                  D (mk a b) (mk a' b') (intro* a b a' b' a* b*) 
                  D _ _ (intro* a b a' b' a* b*) 
            d = c* 
            h* : (z z' : fm) -> (z* : fm* z z') → D z z' z*
            h* = ex* {D} d 
