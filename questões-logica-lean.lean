62 - variables A B: Prop

open classical

example (h1: ¬ A → B) (h2: ¬ B) : A :=
    by_contradiction(
        assume h3: ¬ A,
        have h4: B,
            from h1 h3,
        show false,
            from h2 h4)	


65 - variables A B: Prop


example (h1: ¬ (A ∧ B)) (h2:  B) : ¬ A :=
        assume h3: A,
        have h4: A ∧ B,
            from and.intro h3 h2,
        show false,
            from h1 h4

35 - 

variables A B C : Prop

example (h1: A → B) : ((C∨A)→(B∨C)) :=
    assume h2: (C∨A),
    show (B∨C), from or.elim h2
        (assume h3: C,
        show B ∨ C, from or.inr h3)
        (assume h4: A,
        show B ∨ C, from or.inl (h1 h4))

99 - 

open classical
variables {A B C : Prop}

-- Prove ¬ (A ∧ B) → ¬ A ∨ ¬ B by replacing the sorry's below
-- by proofs.

lemma step1 (h1 : ¬ (A ∨ B)) (h2 : ¬ A) : ¬ A ∧ ¬ B :=
have h5: ¬ B, from (
assume h3: B, 
have h4: A ∨ B, 
from or.inr h3,
show false,
from h1 h4),
show ¬ A ∧ ¬ B, from and.intro h2 h5

lemma step2 (h₁ : ¬ (A ∨ B)) (h2 : ¬ (¬ A ∧ ¬ B)) : false :=
have h3: A, from
  (by_contradiction (assume h5: ¬ A,
    have h6: ¬ A ∧ ¬ B, from step1 h₁ h5,
    show false, from h2 h6)),
have h7: A ∨ B, from or.inl h3,
show false, from h₁ h7

theorem step3 (h : ¬ (A ∨ B)) : ¬ A ∧ ¬ B :=
by_contradiction
  (assume h' : ¬ (¬ A ∧ ¬ B),
    show false, from step2 h h')


example (h1: ¬(¬A ∧ B ∧ ¬C)) (h2:  B) : A ∨ C :=
    by_contradiction(
        assume h3: ¬ (A ∨ C),
        have h5: ¬ A ∧ ¬ C , 
        from step3 h3, 
        have h7: ¬ A, from and.left h5,
        have h8: ¬ C, from and.right h5,
        have h11: B ∧ ¬ C , from and.intro h2 h8,
        have h4: ¬ A ∧ B ∧ ¬ C , from and.intro h7 h11, 
        show false,
        from h1 h4
    )



28 fol -

variable U : Type
variable R : U → Prop
variable S : U → Prop

example (h1: ∀ x, (R x  ↔ S x)) : (∃y,R y) ↔ (∃z,S z) :=

show (∃y,R y) ↔ (∃z, S z), from iff.intro
  (assume h : ∃y,R y,
    show ∃z ,S z, from exists.elim h (
    assume (x : U) (hy: R x), 
    have h3: (R x  ↔ S x), from h1 x,
    have h4: S x, from iff.elim_left h3 hy,
    show ∃z ,S z, from exists.intro x h4))
  (assume h : ∃z,S z ,
    show ∃y,R y , from exists.elim h (
    assume (x : U) (hy: S x), 
    have h3: (R x  ↔ S x), from h1 x,
    have h4: R x, from iff.elim_right h3 hy,
    show ∃z ,R z, from exists.intro x h4))

47 fol - 

section
    variable U : Type
    variable P : U → Prop

    example (h1 : ∀ x,((∃ y, P y) → P x)) : ∀ x, ∀ y,( P y → P x) :=
    assume a,
    assume b, 
    assume h2: P b,
    have h3: (∃ b, P b) → P a, from h1 a ,
    have h4: ∃ b, P b, from exists.intro b h2,
    have h5: P a, from h3 h4 , 
    show P a, from h5
  
end

13 fol - 

variables U Q: Prop
variable P : U → Prop
variable x: U


example (h1: (∀ x,(P x ↔ Q))) : (∀ x,P x )↔ Q :=
show (∀ x,P x ) ↔ Q, from iff.intro
  (assume h : ∀ x,P x ,
    have h3: P x ↔ Q, from h1 x,
    have h4 : P x, from h x,
    show Q, from iff.elim_left h3 h4)
  (assume h : Q ,
    assume y,
    have h3: P x ↔ Q, from h1 x,
    have h4: P x, from iff.elim_right h3 h,
    show P y  , from h4)


31 fol - 

variable U: Prop
variable P : U → Prop
variables i x: U


-- BEGIN

  example  h1: P i  : ¬∀ x,¬ P x :=
  assume h : ∀ x,¬ P x ,
  show false, from (
    have hi : ¬ P i, from h i,
    show false, from hi h1)

-- END


-- LCPO31   P(i) ⊢ ¬∀x.¬P(x)


desafio 773 - refazer

variables A B C D E F: Prop

variable h: false

example: (((A → B) → ((false → C) → D)) → ((D → A) → (E → (F → A))))  :=
    show (((A → B) → ((false → C) → D)) → ((D → A) → (E → (F → A)))), from 
    (assume h1: (A → B) → ((false → C) → D),
    show ((D → A) → (E → (F → A))), from 
    (assume h2: (D → A), show  (E → (F → A)), from 
    (assume h3: E, show (F → A), from 
    (assume h4: F, show A, from false.elim h))))


desafio 386 -

variables A B C D E: Prop

example (h1: (A → B) ∧ (C → D)) (h2: (B ∨ D) → E) (h4: ¬E ): ¬(A ∨ C) :=
    show ¬(A ∨ C), from 
    (assume h: A ∨ C, show false, from or.elim h 
        (assume p1 : A, show false, from 
            (have p2 : A → B, from and.left h1,
             have p3 : B, from p2 p1,
             have p4 : B ∨ D, from or.inl p3,
             have p5 : E, from h2 p4,
             show false, from h4 p5
            )
        ) 
        (assume p1 : C, show false, from 
            (have p2 : C → D, from and.right h1,
             have p3 : D, from p2 p1,
             have p4 : B ∨ D, from or.inr p3,
             have p5 : E, from h2 p4,
             show false, from h4 p5
            )
        )
    )


