module _ where

  rel : (A A' : Set) -> Set₁ 
  rel A A' = A -> A' -> Set

  module id (A : Set) where
    data fm : A -> A -> Set where 
      intro : (a : A) -> fm a a
    ex : { C : (a b : A) -> fm a b -> Set }->
         ( (a : A) -> C _ _  (intro a) )->
         ( a b : A) -> (ab : fm a b) -> C a b ab
    ex {C} c _ _ (intro a) = c a    -- : C a a (intro a)


  module id* (A : Set) (A' : Set) (A* : rel A A') where 

    open id A  public
    open id A' public renaming (fm to fm'; intro to intro'; ex to ex')

    data fm* : (a : A)->(a' : A')->(a* : A* a a')->
               (b : A)->(b' : A')->(b* : A* b b')->
               rel (fm a b) (fm' a' b') where
         intro* : (a : A)->(a' : A')->(a* : A* a a')->
                  -- (b : A)->(b' : A')->(b* : A* b b')->
                  fm* a a' a* a a' a* (intro a) (intro' a')
    ex* : {C* : (a : A) -> (a' : A') -> (a* : A* a a') ->
                (b : A) -> (b' : A') -> (b* : A* b b')->
                (z : fm a b) -> (z' : fm' a' b') -> fm* a a' a* b b' b* z z' -> Set
          } ->
          (c* : (a : A) -> (a' : A') -> (a* : A* a a')->
                C* a a' a* a a' a* (intro a) (intro' a') (intro* a a' a*)
          ) ->
          (a : A) -> (a' : A') -> (a* : A* a a') -> 
          (b : A) -> (b' : A') -> (b* : A* b b')->
          (z : fm a b) -> (z' : fm' a' b') -> (z* : fm* a a' a* b b' b* z z') ->
          C* a a' a* b b' b* z z' z* -- (intro* a a' a*) 
    ex* {C*} c* _ _ _ _ _ _ (intro a) (intro' a') (intro* a a' a*) 
                       = c* a a' a* 

-- the question now: will that give us the interpretation of ex ? 


  module id-in-model (A : Set) (A* : rel A A ) where
    open id* A A A* public
    module _ (C : (a b : A)-> fm a b -> Set)
             (C* : (a a' : A) -> (a* : A* a a') -> (b b' : A)-> (b* : A* b b')->
                (z : fm a b) -> (z' : fm' a' b') -> (z* : fm* a a' a* b b' b* z z') ->
                rel (C a b z) (C a' b' z')
             )  
             (c : (a : A) -> C a a (intro a))
             (c* : (a a' : A)-> (a* : A* a a') ->
                   C* a a' a* a a' a*
                      (intro a) (intro' a') (intro* a a' a*)
                      (ex {C} c a a (intro a)) (ex {C} c a' a' (intro' a'))
             )   
           where   
             h : (a b : A) (ab : fm a b) → C a b ab 
             h = ex {C} c    
             D :  (a a' : A) (a* : A* a a')-> 
                  (b b' : A) (b* : A* b b')-> 
                  (z : fm a b) -> (z' : fm a' b') -> fm* a a' a* b b' b* z z' -> Set
             D a a' a* b b' b* z z' z* = C* a a' a* b b' b* z z' z* (h a b z) (h a' b' z')
             d :  (a a' : A) (a* : A* a a')
                   -> D a a' a* a  a' a* (intro a) (intro' a') (intro* a a' a*) 
             d = c* 
             h* : (a a' : A) (a* : A* a a') 
                  (b b' : A) (b* : A* b b')
                  (z : fm a b) (z' : fm' a' b')
                  (z* : fm* a a' a* b b' b* z z') →
                    D a a' a* b b' b* z z' z* 
             h* = ex* {D} d 



