    id : {X : Set}→ X → X
    id x = x 

    const : {X : Set}{Y : X → Set}→ (x : X) → Y x → X
    const x _ = x

    zero : {X : Set}{Y : (X → X) → Set} → Y id → X → X
    zero _ = id 


    flip : {X : Set}{Y : Set}{Z : X → Y → Set} → ((x : X) (y : Y) → Z x y) → (y : Y)(x : X) → Z x y
    flip f x y = f y x

    comp : {X : Set}{Y : Set}{Z : Y → Set} → (g : (y : Y) → Z y) → (f : X → Y) → (x : X) → Z (f x)
    comp g f x = g (f x)

    exp : {B : Set}{E : B → Set} → (b : B) → (e : (b' : B) → E b') → E b
    exp b e = e b

    times : {X : Set}{Y : Set}{Z : Y → Set} →
            (f : X → Y) → (g : (y : Y) → Z y) → (x : X) → Z (f x)
    times e1 e2 b = exp (exp b e1) e2

    add :  {B : Set}{X : Set}{Y : Set}{Z : Set} → (B → X → Y) → (B → Y → Z) → B → X → Z
    add e1 e2 b  = times (exp b e1) (exp b e2)

