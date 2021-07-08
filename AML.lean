namespace AML
  structure svar := mk :: (name : string)
  structure evar := mk :: (name : string)

  structure box := mk

  inductive var_type
    | evar : evar -> var_type
    | svar : svar -> var_type
    | box : var_type

  inductive pattern : Type
    | var   : var_type -> pattern
    | sym   : string -> pattern
    | app   : pattern -> pattern -> pattern
    | bot   : pattern
    | impl  : pattern -> pattern -> pattern
    | exist : evar -> pattern -> pattern
    | mu    : svar -> pattern -> pattern

  open pattern 

  instance evar_to_pattern : has_coe evar pattern := ⟨λ v, var (var_type.evar v)⟩
  instance svar_to_pattern : has_coe svar pattern := ⟨λ v, var (var_type.svar v)⟩

  instance evar_to_var_type : has_coe evar var_type := ⟨var_type.evar⟩
  instance svar_to_var_type : has_coe svar var_type := ⟨var_type.svar⟩

  instance var_type_to_pattern : has_coe var_type pattern := ⟨var⟩

  notation `⊥` := bot
  notation p `->` q := impl p q
  notation `∃` x `:` p := exist x p

  def not (p : pattern) : pattern := p -> bot
  notation `¬` p := not p

  def or (p q : pattern) : pattern := ¬ p -> q
  notation p `∨` q := or p q
  
  def and (p q : pattern) : pattern := ¬(¬p ∨ ¬q)
  notation p `∧` q := and p q
  
  def top : pattern := not bot
  notation `⊤` := top
  
  def equiv (p q : pattern) : pattern := (p -> q) ∧ (q -> p)
  notation p `<->` q := equiv p q

  def all (x : evar) (p : pattern) : pattern := ¬ (∃x: ¬ p)
  notation `.∀` x `:` p := all x p

  def nu (X : svar) (p : pattern) : pattern := sorry
  
  instance evar.decidable_eq : decidable_eq evar := 
    λ ⟨s₁⟩ ⟨s₂⟩,
        match string.has_decidable_eq s₁ s₂ with
          | is_true p := is_true (congr_arg evar.mk p)
          | is_false p := is_false (λ q, p (evar.mk.inj q))
        end
  instance svar.decidable_eq : decidable_eq svar := 
    λ ⟨s₁⟩ ⟨s₂⟩,
        match string.has_decidable_eq s₁ s₂ with
          | is_true p := is_true (congr_arg svar.mk p)
          | is_false p := is_false (λ q, p (svar.mk.inj q))
        end

  instance var_type.decidable_eq : decidable_eq var_type
    | (var_type.evar v₁) (var_type.evar v₂) := 
        match evar.decidable_eq v₁ v₂ with
          | is_true p := is_true (congr_arg var_type.evar p)
          | is_false p := is_false (λ q, p (var_type.evar.inj q))
        end
    | (var_type.svar v₁) (var_type.svar v₂) :=
        match svar.decidable_eq v₁ v₂ with
          | is_true p := is_true (congr_arg var_type.svar p)
          | is_false p := is_false (λ q, p (var_type.svar.inj q))
        end
    | var_type.box var_type.box := is_true rfl
    | _ _ := is_false (λ h, sorry)

  def FV : pattern -> set var_type
    | (var v) := {v}
    | (sym _) := ∅
    | (app s arg) := (FV s) ∪ (FV arg)
    | bot := ∅
    | (impl p q) := (FV p) ∪ (FV q)
    | (exist x p) := FV p \ {x}
    | (mu X p) := FV p \ {X}

  def pattern.subst (y : pattern) (x : var_type) : pattern -> pattern
    | (var v) := if v = x then y else var x
    | (sym s) := sym s
    | (app s arg) := app (pattern.subst s) (pattern.subst arg)
    | bot := bot
    | (impl p q) := impl (pattern.subst p) (pattern.subst q)
    | (exist z p) := 
        if ↑z = x
          then exist z p
          else if ↑z ∈ FV y then sorry else exist z (pattern.subst p)
    | (mu X p) := sorry

  notation p `[` x `<-` y `]` := pattern.subst y x p

  example :
    let p := (sym "+"), x : evar := ⟨"x"⟩, y : evar := ⟨"y"⟩
     in p[x <- y] = p := rfl
  example :
    let p : evar := ⟨"x"⟩, x : evar := ⟨"x"⟩, y : evar := ⟨"y"⟩
     in p[x <- y] = y := rfl

  def bound (x : var_type) (p : pattern) : Prop := ¬ (x ∈ FV p)
end AML

namespace AML.AppCtx
  open AML
  open AML.pattern

  def isAppCtx : pattern -> Prop
    | (var v) := if v = var_type.box then true else false
    | (sym s) := false
    | (app f arg) := sorry
    | bot := false
    | (impl p q) := false
    | (exist x p) := false
    | (mu X p) := false

  structure appCtx := appCtx ::
    (p : pattern)
    (prop_isAppCtx : isAppCtx p)

  def appCtx.subst (C : appCtx) (p : pattern) : pattern :=
    match C.p with
      | (var v) := sorry
      | (sym s) := sorry
      | (app f arg) := sorry
      | bot := sorry
      | (impl p q) := sorry
      | (exist x p) := sorry
      | (mu X p) := sorry
    end

  notation C `[` p `]` := C.subst p

  def nestedAppCtx : appCtx -> Prop := sorry
end AML.AppCtx

namespace AML.Proof
  open AML
  open AML.pattern
  open AML.AppCtx 

  inductive thm : pattern -> Type*
    -- PL
    | a1 {p q : pattern} : thm (p -> (q -> p))
    | a2 {p q r : pattern} : thm ((p -> (q -> r)) -> ((p -> q) -> (p -> r)))
    | a3 {p q : pattern} : thm ((¬p -> ¬q) -> (q -> p))
    | mp {p q : pattern} (hp : thm p) (hpq : thm (p -> q)) : thm q
    -- FOL
    | varsubst {x y : evar} {p : pattern} : thm ((.∀x: p) -> p [x <- y])
    | all {x : evar} {p q: pattern} : bound x p -> thm ((.∀x: (p -> q)) -> (p -> .∀x: q))
    | gen {x : evar} {p : pattern} (hp : thm p) : thm (.∀x: p)
    -- Frame reasoning
    | propg_bot {C : appCtx} : thm (C[⊥] -> ⊥)
    | propg_disj {C : appCtx} {p q : pattern} : thm (C[p ∨ q] -> C[p] ∨ C[q])
    | propg_exist {C : appCtx} {x : evar} {p : pattern}
        : bound x (C[∃x : p]) -> thm (C[∃x: p] -> ∃x : (C[p]))
    | framing {C : appCtx} {p q : pattern} (h : thm (p -> q)) : thm (C[p] -> C[q])
    -- 
    | existence {x : evar} : thm (∃x : x)
    | singleton {x : evar} {p : pattern} { C₁ C₂ : appCtx }
        : nestedAppCtx C₁ -> nestedAppCtx C₂ -> thm ¬(C₁[x ∧ p] ∧ C₂[x ∧ ¬ p])
    -- TODO: set variable subst
    -- TODO: knaster-tarksi

  notation `⊢` p := thm p

end AML.Proof

namespace AML.Theory
  open AML
  open AML.pattern
  open AML.Proof

  def defined : pattern -> pattern := app (sym "defined")
  notation `⌈` p `⌉` := defined p

  axiom definedness { x : evar } : thm ⌈x⌉

  def total (p : pattern) : pattern := ¬⌈¬p⌉
  notation `⌊` p `⌋` := total p

  def equal (p q : pattern) : pattern := ⌊p <-> q⌋
  def membership (x : var_type) (p : pattern) : pattern := ⌈x ∧ p⌉
  def subset (p q : pattern) : pattern := ⌊p -> q⌋
end AML.Theory
