module _ where

  rel : (A A' : Set) -> Set₁ 
  rel A A' = A -> A' -> Set

  -- Christine Paulin-Mohring style (singleton predicate). Maybe simpler. Incomplete.
  module idPM (A : Set) (a : A) where
    data fmPM : A -> Set where
      introPM : fmPM a

    exPM : {C : (b : A) -> fmPM b -> Set }->
         C a introPM -> (b : A) -> (ab : fmPM b) -> C b ab
    exPM {C} c _ introPM = c   -- : C a introPM
               -- blank can be filled with a or with b

  module idPM* (A : Set) (A' : Set) (A* : rel A A')
               (a : A) (a' : A') (a* : A* a a') where
    open idPM A  a  public
    open idPM A' a' public renaming (fmPM to fmPM' ; introPM to introPM' ; exPM to exPM')

    data fmPM* : rel (fmPM a) (fmPM' a') where
      introPM* : fmPM* introPM introPM'
    exPM* : { C* : (z : fmPM a) -> (z' : fmPM' a') ->
                   (z* : fmPM* introPM introPM') -> Set
            } ->
            (c* : C* introPM introPM' introPM*) ->
            (b : A) -> (b' : A') -> (b* : A* b b') ->
            (z : fmPM b) -> (z' : fmPM' b') -> (z* : fmPM* introPM introPM') ->
            C* introPM introPM' introPM*
    exPM* {C*} c* _ _ _ _ _ introPM* = c* 


{-
  module idPM* (A : Set) (A' : Set) (A* : rel A A')
               (a : A) (a' : A') (a* : A* a a') where
    open idPM A  a  public
    open idPM A' a' public renaming (fmPM to fmPM' ; introPM to introPM' ; exPM to exPM')

    data fmPM* : (b : A) (b' : A') (b* : A* b b') -> rel (fmPM a) (fmPM' a') where
      introPM* : (b : A) (b' : A') (b* : A* b b') -> 
                 fmPM* b b' b* introPM introPM'
    exPM* : { C* : (b : A) -> (b' : A') -> (b* : A* b b') ->
                   (z : fmPM b) -> (z' : fmPM' b') ->
                   (z* : fmPM* b b' b* introPM introPM') -> Set
            } ->
            (c* : C* a a' a* introPM introPM' (introPM* a a' a*)) ->
            (b : A) -> (b' : A') -> (b* : A* b b') ->
            (z : fmPM b) -> (z' : fmPM' b') ->
            (z* : fmPM* a a' a* introPM introPM') -> -- (z* : fmPM* b b' b* introPM introPM') ->
            C* _ _ _ introPM introPM' (introPM* _ _ a*)
    exPM* {C*} c* _ _ _ _ _ (introPM* _ _ _) =  c* 
-}



  module idPM-in-model (A : Set) (A* : rel A A )
                       (a : A) (a' : A) (a* : A* a a')
               where
    open idPM* A A A* a a' a* public
    module _ (C : (b : A)-> fmPM b -> Set)
             (C* : (b : A)(b' : A)(b* : A* b b')
                   (z : fmPM b) (z' : fmPM b') (z* : fmPM* ? ? ) -> -- fmPM* b b' b* {!!} {!!}) -> -- fmPM* b b' b* z z') ->
                   rel (C b z) (C b' z')
             )
             (c : C a introPM )
             (c* : C* a a' a* introPM {!introPM'!} {!!} c {!!})
      where
    {-
             (C* : (a a' : A) -> (a* : A* a a') -> (b b' : A)-> (b* : A* b b')->
                (z : fm a b) -> (z' : fm' a' b') -> (z* : fm* a a' a* b b' b* z z') ->
                rel (C a b z) (C a' b' z')
             )  -- (fm a b) (fm a' b') )
             (c : (a : A) -> C a a (intro a))
             (c* : (a a' : A)-> (a* : A* a a') ->
                   (b b' : A)-> (b* : A* b b') ->
                   (z : fm a b) -> (z' : fm' a' b')-> (z* : fm* a a' a* b b' b* z z')
                   -> -- {!!} -> {!!} -> Set) --
                   C* a a' a* b b' b* z z' z* (ex {C} c a b z) (ex {C} c a' b' z')
             )   -- (ex c _ _ _) (ex c _ _ _) ) -- C* a a' a* a a' a* (intro a) (intro a'))
           where   
             h : (a a' : A) (aa' : fm a a') → C a a' aa' 
             h = ex {C} c    
             D :  (a : A) -> (b : A)-> (ab : A* a b)-> 
                  (a' : A) -> (b' : A)-> (ab' : A* a' b')-> 
                  (z : fm a a') -> (z' : fm b b') -> fm* a b ab a' b' ab' z z' -> Set
             D a b ab a' b' ab' z z' z* = C* a b ab a' b' ab' z z' z* (h a a' z) (h b b' z')
             d : ∀ (a a' : A) (a* : A* a a')
                   (b b' : A) (b* : A* b b')
                   (z : fm a b) (z' : fm' a' b') (z* : fm* a a' a* b b' b* z z') →
                   D a a' a* b  b' b* z z' z* 
             d = c* 
             h* : (a b : A) (ab : A* a b) ->
                  (z : fm a a) (z' : fm' b b) → (z* : fm* a b ab a b ab z z') →
                    D a b ab a b ab z z' z*
             h* = λ a b ab → d a b ab a b ab 



-}
