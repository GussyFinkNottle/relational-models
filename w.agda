module _ where

  module w (A : Set) (B : A -> Set) where

    data fm : Set where
      mk : (a : A) -> (B a -> fm) -> fm

    ex : { C : fm -> Set }->
         ( c : (a : A)-> (f : B a -> fm) -> ((b : B a)-> C (f b)) -> C (mk a f) ) -> 
         (z : fm) -> C z
    ex {C} c (mk a f) = c a f (λ b → ex {C} c (f b)) 

    -- examples (not needed ...) destructors of elements of W A B
    pi0 : fm -> A
    pi0 = ex {λ _ → A} (λ a _ _ → a)
    pi1 : (z : fm) -> B (pi0 z) -> fm 
    pi1 = ex {λ x → B (pi0 x)-> fm} (λ _ f _ → f)

    eta : {X : fm -> fm -> Set}-> ((z : fm) -> X z z) -> (z : fm) -> X z (mk (pi0 z) (pi1 z))
    eta r = ex (λ a f _ → r (mk a f)) 

  module w*  ( A : Set ) ( A' : Set ) ( A* : A -> A' -> Set )
             ( B : A -> Set ) ( B' : A' -> Set )
             ( B* : (a : A) -> (a' : A') -> A* a a' -> B a -> B' a' -> Set )
    where
    open w A B public 
    open w A' B' public renaming (fm to fm'; mk to mk' ; ex to ex' ; pi0 to pi0' ; pi1 to pi1' ; eta to eta') 
    
    data fm* : fm -> fm' -> Set where
      mk* : (a : A) (a' : A') (a* : A* a a') ->
               (f : B a -> fm) (f' : B' a' -> fm') ->
               (f* : (b : B a) (b' : B' a') (b* : B* a a' a* b b') -> fm* (f b) (f' b'))
               -> fm* (mk a f) (mk' a' f') 

    ex* : {D : (z : fm) (z' : fm') -> fm* z z' -> Set }->
          (d : (a : A) -> (a' : A') -> (a* : A* a a') ->
                (f : B a -> fm) -> (f' : B' a' -> fm') ->
                (f* : (b : B a) -> (b' : B' a') -> (b* : B* a a' a* b b') -> fm* (f b) (f' b')) ->
                ( (b  : B a) (b' : B' a') (b* : B* a a' a* b b') -> D (f b) (f' b') (f* b b' b*) 
                ) ->
                D (mk a f) (mk' a' f') (mk* a a' a* f f' f*)) ->
          (z : fm) (z' : fm') (z* : fm* z z') ->
          D z z' z*
    ex* {D} d (mk' a f) (mk' a' f') (mk* a a' a* f f' f*)
       = d a a' a* f f' f*
           λ b b' b* → ex* {D} d (f b) (f' b') (f* b b' b*)

  module w-simple ( A : Set) (A* : A -> A -> Set)
                  ( B : A -> Set) (B* : (a a' : A) -> A* a a' -> B a -> B a' -> Set)
    where
      open w A B public
      data fm* : fm -> fm -> Set where
        mk* : (a a' : A) (a* : A* a a') ->
                 (f : B a -> fm) (f' : B a' -> fm) ->
                 (f* : (b : B a) (b' : B a') (b* : B* a a' a* b b') -> fm* (f b) (f' b'))
               -> fm* (mk a f) (mk a' f') 

      ex* : {D : (z z' : fm) -> fm* z z' -> Set}->
            (d : (a a' : A) -> (a* : A* a a') ->
                 (f : B a → fm)-> (f' : B a' → fm) ->
                 (f* : (b : B a) (b' : B a') → B* a a' a* b b' → fm* (f b) (f' b')) ->
                 ( (b : B a) (b' : B a') (b* : B* a a' a* b b') →
                   D (f b) (f' b') (f* b b' b*)
                 ) ->
                 D (mk a f) (mk a' f') (mk* a a' a* f f' f*)
            ) ->
            (z z' : fm) -> (z* : fm* z z') -> D z z' z*
      ex* {D} d (mk _ _) (mk _ _) (mk* a a' a* f f' f*)
         = d a a' a* f f' f*
           λ b b' b* → ex* {D} d (f b) (f' b') (f* b b' b*)
        

  module w-in-model ( A : Set ) ( A* : A -> A -> Set )
                    ( B : A -> Set ) ( B* : (a a' : A)-> A* a a' -> B a -> B a' -> Set )
    where
    open w-simple A A* B B* public
 -- open w* A A A* B B B* public
    module _ (C : fm -> Set)
             (C* : (z z' : fm)-> (z* : fm* z z')-> C z -> C z' -> Set)
             (c : (a : A)-> (f : B a -> fm) -> ((b : B a)-> C (f b)) -> C (mk a f))
             (c* : (a a' : A) (a* : A* a a') (f : B a → fm) (f' : B a' → fm)
                   (f* : (b : B a) (b' : B a') → B* a a' a* b b' → fm* (f b) (f' b')) →
                   ( (b : B a) (b' : B a') (b* : B* a a' a* b b') →
                      C* (f b) (f' b') (f* b b' b*) (ex {C} c (f b)) (ex {C} c (f' b'))
                   ) →
                   C* (mk a f) (mk a' f') (mk* a a' a* f f' f*)
                      (c a f (λ b → ex {C} c (f b))) (c a' f' (λ b → ex {C} c (f' b)))
             ) where
          h : (z : fm) -> C z
          h = ex {C} c
          D : (z z' : fm)-> (z* : fm* z z')-> Set
          D z z' z* = C* z z' z* (h z) (h z')
          d : (a a' : A) (a* : A* a a') (f : B a → fm) (f' : B a' → fm)
                (f* : (b : B a) (b' : B a') → B* a a' a* b b' → fm* (f b) (f' b')) →
                ((b : B a) (b' : B a') (b* : B* a a' a* b b') →
--                 C* (f b) (f' b') (f* b b' b*) (h (f b)) (h (f' b'))
                   D (f b) (f' b') (f* b b' b*)
                ) →
--                C* (mk a f) (mk a' f') (mk* a a' a* f f' f*)
--                   (c a f (λ b → h (f b))) (c a' f' (λ b → h (f' b)))
                  D (mk a f) (mk a' f') (mk* a a' a* f f' f*)
          d = c*
          h* :  (z z' : fm)-> (z* : fm* z z')-> D z z' z*
          h* = ex* {D} d 
