module _ where

  open import combinators

  module s (A : Set)  where

   -- I would/should call fm "S A", mk₀ "o", and (mk₁ a) "s a".

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
      
    ex* : {D : (z : fm) -> (z' : fm') -> pow (fm* z z')}->
           (s0 : D mk₀ mk₀' mk*₀) ->
           (s1 : ( a : A)->(a' : A')-> (a* : A* a a') -> D (mk₁ a) (mk₁' a') (mk*₁ a a' a*)) ->
           (z : fm)->(z' : fm') -> (z* : fm* z z')-> D z z' z*
    ex* {D} s0 s1 _ _ mk*₀ = s0
    ex* {D} s0 s1 _ _ (mk*₁ a a' x) = s1 a a' x 
    
    -- I suppose there's some kind of large eliminator too ...

  -- interpret the s-eliminator in the model
  module s-in-model (A : Set) (A* : rel A A) where
    open s* A A A* public
    module _
           (C : pow fm)
           (C* : (z z' : fm)-> fm* z z' -> rel (C z) (C z'))
           (c₀ : C mk₀)
           (c₀* : C* mk₀ mk₀ mk*₀ c₀ c₀)
           (c₁ : (a : A)-> C (mk₁ a))
           (c₁* : (a a' : A)->(a* : A* a a')-> C* (mk₁ a) (mk₁ a') (mk*₁ a a' a*) (c₁ a) (c₁ a')) where
      h : (z : fm) → C z
      h = ex {C} c₀ c₁
      D : (z z' : fm)-> pow (fm* z z')
      D z z' z* = C* z z' z* (h z) (h z') 
      d₀ : C* mk₀ mk₀ mk*₀ c₀ c₀
      d₀ = c₀* 
      d₁ : (a a' : A) (a* : A* a a') →
             C* (mk₁ a) (mk₁ a') (mk*₁ a a' a*) (c₁ a) (c₁ a')
      d₁ = c₁* 
      h* : (z z' : fm) -> (z* : fm* z z') → D z z' z*
      h* = ex* {D} d₀ d₁ 
           
