namespace AML
  -- Encoding variables with De Brujin indices
  structure evar := mk :: (dbi : ℕ) /-^ Element variables-/
  structure svar := mk :: (dbi : ℕ) /-^ Set variables -/

  structure box := mk /-^ Box placeholder for application contexts -/

  /-- AML has two types of variables: element variables and set variables.
    - TODO: Expand comment
    -/
  inductive var_type
    | evar : evar -> var_type
    | svar : svar -> var_type
    | box : var_type

  /-- AML formulas, which we call patterns because of the pattern matching semantics.
    -/
  inductive pattern : Type
    | var   : var_type -> pattern 
    | evar : evar -> pattern
    | svar : svar -> pattern
    | sym   : string -> pattern
    | app   : pattern -> pattern -> pattern
    | bot   : pattern
    | impl  : pattern -> pattern -> pattern
    | exist : evar -> pattern -> pattern
    | mu    : svar -> pattern -> pattern

  open pattern 

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

  namespace AML.instances
    instance evar_to_pattern : has_coe evar pattern := ⟨λ v, var (var_type.evar v)⟩
    instance svar_to_pattern : has_coe svar pattern := ⟨λ v, var (var_type.svar v)⟩

    instance evar_to_var_type : has_coe evar var_type := ⟨var_type.evar⟩
    instance svar_to_var_type : has_coe svar var_type := ⟨var_type.svar⟩

    instance var_type_to_pattern : has_coe var_type pattern := ⟨var⟩

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
  end AML.instances
  
  /-- The set of all free variables in a pattern -/
  def pattern.FV : pattern -> set var_type
    | (var v) := {v}
    | (sym _) := ∅
    | (app s arg) := s.FV ∪ arg.FV
    | bot := ∅
    | (impl p q) := p.FV ∪ q.FV
    | (exist x p) := p.FV \ {x}
    | (mu X p) := p.FV \ {X}

  /-- Substitute variable `x` with pattern `y` in given pattern.
    - TODO: Fix this
    -/
  def pattern.subst (y : pattern) (x : var_type) : pattern -> pattern
    | (var v) := if v = x then y else var x
    | (sym s) := sym s
    | (app s arg) := app (pattern.subst s) (pattern.subst arg)
    | bot := bot
    | (impl p q) := impl (pattern.subst p) (pattern.subst q)
    | (exist z p) := 
        if ↑z = x
          then exist z p
          else if ↑z ∈ y.FV then sorry else exist z (pattern.subst p)
    | (mu X p) := sorry

  notation p `[` y `//` x `]` := pattern.subst y x p

  section
    example :
      let p := (sym "+"), x : evar := ⟨"x"⟩, y : evar := ⟨"y"⟩
      in p[x <- y] = p := rfl
    example :
      let p : evar := ⟨"x"⟩, x : evar := ⟨"x"⟩, y : evar := ⟨"y"⟩
      in p[x <- y] = y := rfl
  end

  def pattern.hasBound (x : var_type) (p : pattern) : Prop := ¬ (x ∈ p.FV)

  /-- This should apply to μX.φ where X has to be positive in φ. It should not be nested
    - an odd number of times on the left of an implication φ₁ -> φ₂.
    -/
  def positive (X : svar) (φ : pattern) : Prop := sorry
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

  def appCtx.hasBound (x : var_type) (C : appCtx) : Prop := sorry
end AML.AppCtx

namespace AML.Proof
  open AML
  open AML.pattern
  open AML.AppCtx

  variables {p q r : pattern}
  variables { x y : evar }
  variables {C C₁ C₂ : appCtx}

  inductive thm : pattern -> Type*
    -- Propositional logic
    | a1 : thm (p -> (q -> p))
    | a2 : thm ((p -> (q -> r)) -> ((p -> q) -> (p -> r)))
    | a3 : thm ((¬p -> ¬q) -> (q -> p))
    | mp : thm p -> thm (p -> q) -> thm q
    -- FOL
    | ex_quan : thm (p[y//x] -> (∃x:p))
    | ex_gen : q.hasBound x -> thm (p -> q) -> thm (∃x:p -> q)
    -- Frame reasoning
    | propg_bot : thm (C[⊥] -> ⊥)
    | propg_disj : thm (C[p ∨ q] -> C[p] ∨ C[q])
    | propg_exist : C.hasBound x -> thm (C[∃x: p] -> ∃x : (C[p]))
    | framing : thm (p -> q) -> thm (C[p] -> C[q])
    -- Technical rules
    | existence : thm (∃x:x)
    | singleton : nestedAppCtx C₁ -> nestedAppCtx C₂ -> thm ¬(C₁[x ∧ p] ∧ C₂[x ∧ ¬ p])
    -- TODO: set variable subst
    -- TODO: pre-fixpoint
    -- TODO: knaster-tarksi

  notation `⊢` p := thm p

end AML.Proof

namespace AML.Semantics
  notation `𝒫` t := set t

  variable symbol : Type

  /-- A model that a specific pattern is evaluated in.
    -/
  structure model :=
    (domain : Type)
    (application : domain -> domain -> 𝒫 domain)
    /-^ Interpretation of symbol application -/
    (symbol_interp : symbol -> set domain)
    /-^ Interpretation of symbol -/

  variable {α : Type}
  variable {M : model α}

  def theory := set AML.pattern

  def full : 𝒫 M.domain := sorry
  def empty : 𝒫 M.domain := ∅
  
  /- Since pattern evaluation is not two-valued, we can take ∅ to represent false and
   - the full domain to represent truth.
   -/
  notation `⊤` := full
  notation `⊥` := empty

  /-- The pointwisely extension over sets of symbol application over elements. -/
  def set_app : 𝒫 M.domain -> 𝒫 M.domain -> 𝒫 M.domain := sorry

  /-- Evaluation of element variables, ranging over specific elements in the domain -/
  def evar_eval : AML.evar -> M.domain := sorry

  /-- Evaluation of set variables, ranging over subsets of the domain. -/
  def svar_eval : AML.svar -> 𝒫 M.domain := sorry

  /-- Extending valuations to patterns -/
  def pattern_eval : AML.pattern -> 𝒫 M.domain
    | (AML.pattern.evar v) := {evar_eval v}
    | (AML.pattern.svar v) := svar_eval v
    | AML.pattern.bot := ∅
    | (AML.pattern.sym s) := sorry
    | (AML.pattern.app f arg) := sorry
    | (AML.pattern.impl p q) := sorry
    | (AML.pattern.exist x p) := sorry
    | (AML.pattern.mu X p) := sorry

  /-- A pattern is a predicate if it evaluates to ⊤ or ⊥. -/
  def predicate (φ : AML.pattern) : Prop := pattern_eval φ = ⊤ ∨ pattern_eval φ = ⊥

  /-- A model satisfies a given pattern if the pattern evaluates to ⊤ in that model. -/
  def satisfies_pattern (M : model α) (φ : AML.pattern) : Prop := pattern_eval φ = ⊤
  notation M `⊧` φ := satisfies_pattern M φ

  /-- A model satisfies a set of patterns, called a theory, if all patterns evaluate
    - to ⊤ in that model.
    -/
  def satisfies_theory (M : model α) (Γ : theory) : Prop := sorry
  notation M `⊧` Γ := satisfies_theory M Γ
end AML.Semantics

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
