module _ where

  open import combinators

  module s (A : Set)  where

    data fm : Set where
      mk₀ : fm
      mk₁ : A → fm 

    ex : { C : pow fm }→
         ( c₀ : C mk₀)-> 
         ( c₁ : (a : A) -> C (mk₁ a))-> 
         (z : fm) → C z
    ex {C} c₀ c₁ mk₀ = c₀
    ex {C} c₀ c₁ (mk₁ a) = c₁ a 

    private Ex : { D : Set₁ }-> 
                 ( c₀ : D)-> 
                 ( c₁ : A -> D)-> 
                 (z : fm) → D
    Ex {C} c₀ c₁ mk₀ = c₀
    Ex {C} c₀ c₁ (mk₁ a) = c₁ a 

-- I need to make a relation...

  module s* (A : Set) (A' : Set) (A* : rel A A') where
    open s A  public
    open s A' public renaming (fm to fm' ; mk₀ to mk₀' ; mk₁ to mk₁' ; ex to ex' )

    data fm* : rel  (s.fm A) (s.fm A') where
      mk*₀ : fm* s.mk₀ s.mk₀ 
      mk*₁ : (a : A)(a' : A') -> A* a a' -> fm* (mk₁ a) (mk₁' a')
      
    ex* : {D : (z : fm) -> (z' : fm') -> fm* z z' -> Set}->
           (s0 : D mk₀ mk₀' mk*₀) ->
           (s1 : ( a : A)->(a' : A')-> (a* : A* a a') -> D (mk₁ a) (mk₁' a') (mk*₁ a a' a*)) ->
           (z : fm)->(z' : fm') -> (z* : fm* z z')-> D z z' z*
    ex* {D} s0 s1 _ _ mk*₀ = s0
    ex* {D} s0 s1 _ _ (mk*₁ a a' x) = s1 a a' x 
    
