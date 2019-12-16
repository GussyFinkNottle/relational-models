
module pi where 
  module pi (A : Set) (B : A -> Set) where  -- cf sigma module at end of this file

    data fm : Set where                   -- formation
      mk :  (b : (a : A)-> B a) -> fm     -- introduction

    ex : { C : fm -> Set }->              -- elimination
         ( (b : (a : A) -> B a) -> C (mk b) )->
         ( z : fm )-> C z
    ex c (mk b) = c b                  -- computation

    Ex : { D : Set₁ }->                -- large version: mere iterator (no dependency).
         (d : (b : (a : A)-> B a) -> D )->
         (z : fm) -> D
    Ex d (mk x) = d x
    
    {- examples of use of ex -}

    -- flip of application (argument before function)
    at : (a : A)-> fm -> B a
    at a  = ex -- {λ _ → B a}   
               (λ b → b a)

    -- "propositional" eta, Leibnitz'd to avoid identity type ...
    eta : {X : fm -> fm -> Set}->
          ( (z : fm)-> X z z )->
          (z : fm)-> X z (mk λ a → at a z)
    eta -- {X}
            r = ex -- {λ z → X z (mk (λ x → at x z))}
                   (λ b → r (mk b))

    -- a local definition just for the sake of subtleties about etaAlt, following
    private id : {X : Set}-> X -> X
            id x = x

    etaAlt : (X : fm -> Set)->     -- a bit more Leibnitzic
          (z : fm)-> X z -> X (mk λ a → at a z) 
    etaAlt X = ex -- { λ z → X z -> X (mk (λ a → at a z)) }
                  -- (λ _ → id) -- this is actually the combinator 'zero'
                  (λ _ → id {X (mk _)}) -- this is actually the combinator 'zero'
                  -- λ b → id {X (mk b)} -- {X (mk (λ a → at a (mk b)))}

  module pi* ( A : Set ) ( A' : Set ) 
             ( A* : A -> A' -> Set )
             ( B : A -> Set ) ( B' : A' -> Set )
             ( B* : (a : A)->(a' : A')-> A* a a' -> B a -> B' a' -> Set )
        where
    open pi A B public 
    open pi A' B' public renaming (fm to fm'; mk to mk' ; ex to ex'; at to at' ; eta to eta'; etaAlt to etaAlt')
                         hiding (id ; Ex )
    data fm* : fm -> fm' -> Set where
      mk* : ( b : (a : A)-> B a )->
               ( b' : (a' : A') -> B' a' ) ->
               ( (a : A)-> (a' : A')-> (a* : A* a a') -> B* a a' a* (b a) (b' a') )
               -> fm* (mk b) (mk' b')   -- righteously episcopalian

    ex* : { D : (z : fm) -> (z' : fm') -> fm* z z' -> Set }->
          ( d : (b  : (a : A)-> B a)  ->  (b' : (a' : A') -> B' a') ->
                (b* : (a : A) -> (a' : A') ->
                      (a* : A* a a') → B* a a' a* (b a) (b' a')
                ) ->
                D (mk b) (mk' b') (mk* b b' b*)
          ) ->
          ( z : fm ) -> (z' : fm') -> (z* : fm* z z') -> D z z' z*
    ex* {D} d _ _ (mk* b b' b*) = d b b' b* -- blanks are (mk b) and (intro' b')

    -- application respects relations in each argument.
    at* : (a : A) -> (a' : A') -> (a* : A* a a') ->
          (z : fm) -> (z' : fm') -> fm* z z' ->
          B* a a' a* (at a z) (at' a' z')
    at* a a' a* 
       = let H : (z : fm) (z' : fm') (z* : fm* z z') → Set 
             H z z' z* = B* a a' a* (at a z) (at' a' z') 
             h : (b : (a : A) → B a) -> (b' : (a' : A') → B' a') ->
                 (b* : (a : A) (a' : A') (a* : A* a a') → B* a a' a* (b a) (b' a')) →
                 B* a a' a* (at a (mk b)) (at' a' (mk' b'))
             h b b' b* = b* a a' a*
         in
         ex* {H} h 

  module pi-in-model (A : Set )
           (A* : A -> A -> Set)
           (B : A -> Set)
           (B* : (a a' : A)-> A* a a' -> B a -> B a' -> Set)
         where
    open pi* A A A* B B B* public hiding (fm' ; mk' ; ex' ; at' ; eta' )
    module _ (C : fm -> Set)
             (C* : (z : fm)->(z' : fm)->(z* : fm* z z')-> C z -> C z' -> Set)   -- C, in the model
             (c : (b : (a : A)-> B a)-> C (mk b))
             (c* : (b b' : (a : A)-> B a) ->                                    -- c in the model (??)
                   (b* : (a a' : A)-> (a* : A* a a')-> B* a a' a* (b a) (b' a'))->
                   C* (mk b) (mk b') (mk* b b' b*) (c b) (c b'))
          where
            h : (z : fm) -> C z
            h = ex {C} c
            D : (z : fm) -> (z' : fm) -> fm* z z' -> Set
            D z z' z* = C* z z' z* (h z) (h z')                 -- choose right D ...
            d : (b b' : (a : A)-> B a)->                        -- ... and d
                (b*  : (a a' : A) -> (a* : A* a a') → B* a a' a* (b a) (b' a')) ->
                  D (mk _) (mk _) (mk* b b' b*)
            d = c* 
            h* : (z z' : fm) -> (z* : fm* z z') → D z z' z*
            h* = ex* {D} d 
