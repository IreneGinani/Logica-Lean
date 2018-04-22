
section 

-- Questao 62 Logica proposicional : LCP-62 ¬A → B, ¬B ⊢ A

variables A B: Prop

open classical

example (h1: ¬ A → B) (h2: ¬ B) : A :=
    by_contradiction(
        assume h3: ¬ A,
        have h4: B,
            from h1 h3,
        show false,
            from h2 h4) 

end

section

-- Questao 65 Logica proposicional : LCP-65  ¬(A∧B), B ⊢ ¬A

variables A B: Prop


example (h1: ¬ (A ∧ B)) (h2:  B) : ¬ A :=
        assume h3: A,
        have h4: A ∧ B,
            from and.intro h3 h2,
        show false,
            from h1 h4

end

section 

-- Questao 35 Logica proposicional : LCP­35: (A→B) ⊢ ((C∨A)→(B∨C))

variables A B C : Prop

example (h1: A → B) : ((C∨A)→(B∨C)) :=
    assume h2: (C∨A),
    show (B∨C), from or.elim h2
        (assume h3: C,
        show B ∨ C, from or.inr h3)
        (assume h4: A,
        show B ∨ C, from or.inl (h1 h4))

end 


section 

-- Questao 99 Logica proposicional : LCP-99 ¬(¬A∧B∧¬C), B ⊢ (A∨C)

open classical
variables {A B C : Prop}

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

end

section

-- Questao 28 Logica de primeira ordem  :  ∀x,(R(x)↔S(x)) ⊢ ∃y,R(y)↔∃z,S(z)

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

end 

section

-- Questao 47 Logica de primeira ordem  :  ∀x.(∃y.P(y)→P(x)) ⊢ ∀x.∀y.(P(y)→P(x))
   
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

section

-- Questao 13 Logica de primeira ordem  :   ∀x.(P(x)↔Q) ⊢ (∀x.P(x))↔Q

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

end

section

-- Questao 13 Logica de primeira ordem : LCPO31   P(i) ⊢ ¬∀x.¬P(x)

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



end

section

-- Questao 773 dos desafios : ⊢ (((A → B) → ((⊥ → C) → D)) → ((D → A) → (E → (F → A))))

open classical

variables A B C D E F: Prop

example: ((A → B) → ((false → C) → D)) → ((D → A) → (E → (F → A)))  :=
    show (((A → B) → ((false → C) → D)) → ((D → A) → (E → (F → A)))), from 
    (
        assume h1: (A → B) → ((false → C) → D),
        show (D → A) → (E → (F → A)), from (
            assume h2: (D → A), show  (E → (F → A)), from (
                assume h3: E, show (F → A), from (
                    assume h4: F,
                    
                    have hfalcd : (false → C) → D, from (
                        have hab : A → B, from (
                            assume ha : A,
                            show B, from sorry
                        ),
                        show (false → C) → D, from h1 hab
                    ),
                    
                    have hfalc : false → C, from (
                        assume hfal : false,
                        show C, from by_contradiction (
                            assume hnc : ¬ C,
                            show false, from hfal
                        )
                    ),
                    
                    have hd : D, from hfalcd hfalc,

                    show A, from h2 hd
                )
            )
        )
    )
end

section

-- Questao 386 dos desafios : ((A → B) ∧ (C → D)), ((B ∨ D) → E), (¬E) ⊢ ¬(A ∨ C)

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

end




link: 

https://leanprover.github.io/live/3.3.0/#code=%0Asection%20%0A%0A--%20Questao%2062%20Logica%20proposicional%20:%20LCP-62%20%C2%ACA%20%E2%86%92%20B,%20%C2%ACB%20%E2%8A%A2%20A%0A%0Avariables%20A%20B:%20Prop%0A%0Aopen%20classical%0A%0Aexample%20(h1:%20%C2%AC%20A%20%E2%86%92%20B)%20(h2:%20%C2%AC%20B)%20:%20A%20:=%0A%20%20%20%20by_contradiction(%0A%20%20%20%20%20%20%20%20assume%20h3:%20%C2%AC%20A,%0A%20%20%20%20%20%20%20%20have%20h4:%20B,%0A%20%20%20%20%20%20%20%20%20%20%20%20from%20h1%20h3,%0A%20%20%20%20%20%20%20%20show%20false,%0A%20%20%20%20%20%20%20%20%20%20%20%20from%20h2%20h4)%09%0A%0Aend%0A%0Asection%0A%0A--%20Questao%2065%20Logica%20proposicional%20:%20LCP-65%20%20%C2%AC(A%E2%88%A7B),%20B%20%E2%8A%A2%20%C2%ACA%0A%0Avariables%20A%20B:%20Prop%0A%0A%0Aexample%20(h1:%20%C2%AC%20(A%20%E2%88%A7%20B))%20(h2:%20%20B)%20:%20%C2%AC%20A%20:=%0A%20%20%20%20%20%20%20%20assume%20h3:%20A,%0A%20%20%20%20%20%20%20%20have%20h4:%20A%20%E2%88%A7%20B,%0A%20%20%20%20%20%20%20%20%20%20%20%20from%20and.intro%20h3%20h2,%0A%20%20%20%20%20%20%20%20show%20false,%0A%20%20%20%20%20%20%20%20%20%20%20%20from%20h1%20h4%0A%0Aend%0A%0Asection%20%0A%0A--%20Questao%2035%20Logica%20proposicional%20:%20LCP%C2%AD35:%20(A%E2%86%92B)%20%E2%8A%A2%20((C%E2%88%A8A)%E2%86%92(B%E2%88%A8C))%0A%0Avariables%20A%20B%20C%20:%20Prop%0A%0Aexample%20(h1:%20A%20%E2%86%92%20B)%20:%20((C%E2%88%A8A)%E2%86%92(B%E2%88%A8C))%20:=%0A%20%20%20%20assume%20h2:%20(C%E2%88%A8A),%0A%20%20%20%20show%20(B%E2%88%A8C),%20from%20or.elim%20h2%0A%20%20%20%20%20%20%20%20(assume%20h3:%20C,%0A%20%20%20%20%20%20%20%20show%20B%20%E2%88%A8%20C,%20from%20or.inr%20h3)%0A%20%20%20%20%20%20%20%20(assume%20h4:%20A,%0A%20%20%20%20%20%20%20%20show%20B%20%E2%88%A8%20C,%20from%20or.inl%20(h1%20h4))%0A%0Aend%20%0A%0A%0Asection%20%0A%0A--%20Questao%2099%20Logica%20proposicional%20:%20LCP-99%20%C2%AC(%C2%ACA%E2%88%A7B%E2%88%A7%C2%ACC),%20B%20%E2%8A%A2%20(A%E2%88%A8C)%0A%0Aopen%20classical%0Avariables%20%7BA%20B%20C%20:%20Prop%7D%0A%0Alemma%20step1%20(h1%20:%20%C2%AC%20(A%20%E2%88%A8%20B))%20(h2%20:%20%C2%AC%20A)%20:%20%C2%AC%20A%20%E2%88%A7%20%C2%AC%20B%20:=%0Ahave%20h5:%20%C2%AC%20B,%20from%20(%0Aassume%20h3:%20B,%20%0Ahave%20h4:%20A%20%E2%88%A8%20B,%20%0Afrom%20or.inr%20h3,%0Ashow%20false,%0Afrom%20h1%20h4),%0Ashow%20%C2%AC%20A%20%E2%88%A7%20%C2%AC%20B,%20from%20and.intro%20h2%20h5%0A%0Alemma%20step2%20(h%E2%82%81%20:%20%C2%AC%20(A%20%E2%88%A8%20B))%20(h2%20:%20%C2%AC%20(%C2%AC%20A%20%E2%88%A7%20%C2%AC%20B))%20:%20false%20:=%0Ahave%20h3:%20A,%20from%0A%20%20(by_contradiction%20(assume%20h5:%20%C2%AC%20A,%0A%20%20%20%20have%20h6:%20%C2%AC%20A%20%E2%88%A7%20%C2%AC%20B,%20from%20step1%20h%E2%82%81%20h5,%0A%20%20%20%20show%20false,%20from%20h2%20h6)),%0Ahave%20h7:%20A%20%E2%88%A8%20B,%20from%20or.inl%20h3,%0Ashow%20false,%20from%20h%E2%82%81%20h7%0A%0Atheorem%20step3%20(h%20:%20%C2%AC%20(A%20%E2%88%A8%20B))%20:%20%C2%AC%20A%20%E2%88%A7%20%C2%AC%20B%20:=%0Aby_contradiction%0A%20%20(assume%20h'%20:%20%C2%AC%20(%C2%AC%20A%20%E2%88%A7%20%C2%AC%20B),%0A%20%20%20%20show%20false,%20from%20step2%20h%20h')%0A%0A%0Aexample%20(h1:%20%C2%AC(%C2%ACA%20%E2%88%A7%20B%20%E2%88%A7%20%C2%ACC))%20(h2:%20%20B)%20:%20A%20%E2%88%A8%20C%20:=%0A%20%20%20%20by_contradiction(%0A%20%20%20%20%20%20%20%20assume%20h3:%20%C2%AC%20(A%20%E2%88%A8%20C),%0A%20%20%20%20%20%20%20%20have%20h5:%20%C2%AC%20A%20%E2%88%A7%20%C2%AC%20C%20,%20%0A%20%20%20%20%20%20%20%20from%20step3%20h3,%20%0A%20%20%20%20%20%20%20%20have%20h7:%20%C2%AC%20A,%20from%20and.left%20h5,%0A%20%20%20%20%20%20%20%20have%20h8:%20%C2%AC%20C,%20from%20and.right%20h5,%0A%20%20%20%20%20%20%20%20have%20h11:%20B%20%E2%88%A7%20%C2%AC%20C%20,%20from%20and.intro%20h2%20h8,%0A%20%20%20%20%20%20%20%20have%20h4:%20%C2%AC%20A%20%E2%88%A7%20B%20%E2%88%A7%20%C2%AC%20C%20,%20from%20and.intro%20h7%20h11,%20%0A%20%20%20%20%20%20%20%20show%20false,%0A%20%20%20%20%20%20%20%20from%20h1%20h4%0A%20%20%20%20)%0A%0Aend%0A%0Asection%0A%0A--%20Questao%2028%20Logica%20de%20primeira%20ordem%20%20:%20%20%E2%88%80x,(R(x)%E2%86%94S(x))%20%E2%8A%A2%20%E2%88%83y,R(y)%E2%86%94%E2%88%83z,S(z)%0A%0Avariable%20U%20:%20Type%0Avariable%20R%20:%20U%20%E2%86%92%20Prop%0Avariable%20S%20:%20U%20%E2%86%92%20Prop%0A%0Aexample%20(h1:%20%E2%88%80%20x,%20(R%20x%20%20%E2%86%94%20S%20x))%20:%20(%E2%88%83y,R%20y)%20%E2%86%94%20(%E2%88%83z,S%20z)%20:=%0A%0Ashow%20(%E2%88%83y,R%20y)%20%E2%86%94%20(%E2%88%83z,%20S%20z),%20from%20iff.intro%0A%20%20(assume%20h%20:%20%E2%88%83y,R%20y,%0A%20%20%20%20show%20%E2%88%83z%20,S%20z,%20from%20exists.elim%20h%20(%0A%20%20%20%20assume%20(x%20:%20U)%20(hy:%20R%20x),%20%0A%20%20%20%20have%20h3:%20(R%20x%20%20%E2%86%94%20S%20x),%20from%20h1%20x,%0A%20%20%20%20have%20h4:%20S%20x,%20from%20iff.elim_left%20h3%20hy,%0A%20%20%20%20show%20%E2%88%83z%20,S%20z,%20from%20exists.intro%20x%20h4))%0A%20%20(assume%20h%20:%20%E2%88%83z,S%20z%20,%0A%20%20%20%20show%20%E2%88%83y,R%20y%20,%20from%20exists.elim%20h%20(%0A%20%20%20%20assume%20(x%20:%20U)%20(hy:%20S%20x),%20%0A%20%20%20%20have%20h3:%20(R%20x%20%20%E2%86%94%20S%20x),%20from%20h1%20x,%0A%20%20%20%20have%20h4:%20R%20x,%20from%20iff.elim_right%20h3%20hy,%0A%20%20%20%20show%20%E2%88%83z%20,R%20z,%20from%20exists.intro%20x%20h4))%0A%0Aend%20%0A%0Asection%0A%0A--%20Questao%2047%20Logica%20de%20primeira%20ordem%20%20:%20%20%E2%88%80x.(%E2%88%83y.P(y)%E2%86%92P(x))%20%E2%8A%A2%20%E2%88%80x.%E2%88%80y.(P(y)%E2%86%92P(x))%0A%20%20%20%0A%20%20%20%20variable%20U%20:%20Type%0A%20%20%20%20variable%20P%20:%20U%20%E2%86%92%20Prop%0A%0A%20%20%20%20example%20(h1%20:%20%E2%88%80%20x,((%E2%88%83%20y,%20P%20y)%20%E2%86%92%20P%20x))%20:%20%E2%88%80%20x,%20%E2%88%80%20y,(%20P%20y%20%E2%86%92%20P%20x)%20:=%0A%20%20%20%20assume%20a,%0A%20%20%20%20assume%20b,%20%0A%20%20%20%20assume%20h2:%20P%20b,%0A%20%20%20%20have%20h3:%20(%E2%88%83%20b,%20P%20b)%20%E2%86%92%20P%20a,%20from%20h1%20a%20,%0A%20%20%20%20have%20h4:%20%E2%88%83%20b,%20P%20b,%20from%20exists.intro%20b%20h2,%0A%20%20%20%20have%20h5:%20P%20a,%20from%20h3%20h4%20,%20%0A%20%20%20%20show%20P%20a,%20from%20h5%0A%20%20%0Aend%0A%0Asection%0A%0A--%20Questao%2013%20Logica%20de%20primeira%20ordem%20%20:%20%20%20%E2%88%80x.(P(x)%E2%86%94Q)%20%E2%8A%A2%20(%E2%88%80x.P(x))%E2%86%94Q%0A%0Avariables%20U%20Q:%20Prop%0Avariable%20P%20:%20U%20%E2%86%92%20Prop%0Avariable%20x:%20U%0A%0A%0Aexample%20(h1:%20(%E2%88%80%20x,(P%20x%20%E2%86%94%20Q)))%20:%20(%E2%88%80%20x,P%20x%20)%E2%86%94%20Q%20:=%0Ashow%20(%E2%88%80%20x,P%20x%20)%20%E2%86%94%20Q,%20from%20iff.intro%0A%20%20(assume%20h%20:%20%E2%88%80%20x,P%20x%20,%0A%20%20%20%20have%20h3:%20P%20x%20%E2%86%94%20Q,%20from%20h1%20x,%0A%20%20%20%20have%20h4%20:%20P%20x,%20from%20h%20x,%0A%20%20%20%20show%20Q,%20from%20iff.elim_left%20h3%20h4)%0A%20%20(assume%20h%20:%20Q%20,%0A%20%20%20%20assume%20y,%0A%20%20%20%20have%20h3:%20P%20x%20%E2%86%94%20Q,%20from%20h1%20x,%0A%20%20%20%20have%20h4:%20P%20x,%20from%20iff.elim_right%20h3%20h,%0A%20%20%20%20show%20P%20y%20%20,%20from%20h4)%0A%0Aend%0A%0Asection%0A%0A--%20Questao%2013%20Logica%20de%20primeira%20ordem%20:%20LCPO31%20%20%20P(i)%20%E2%8A%A2%20%C2%AC%E2%88%80x.%C2%ACP(x)%0A%0Avariable%20U:%20Prop%0Avariable%20P%20:%20U%20%E2%86%92%20Prop%0Avariables%20i%20x:%20U%0A%0A%0A--%20BEGIN%0A%0A%20%20example%20%20h1:%20P%20i%20%20:%20%C2%AC%E2%88%80%20x,%C2%AC%20P%20x%20:=%0A%20%20assume%20h%20:%20%E2%88%80%20x,%C2%AC%20P%20x%20,%0A%20%20show%20false,%20from%20(%0A%20%20%20%20have%20hi%20:%20%C2%AC%20P%20i,%20from%20h%20i,%0A%20%20%20%20show%20false,%20from%20hi%20h1)%0A%0A--%20END%0A%0A%0A%0Aend%0A%0Asection%0A%0A--%20Questao%20773%20dos%20desafios%20:%20%E2%8A%A2%20(((A%20%E2%86%92%20B)%20%E2%86%92%20((%E2%8A%A5%20%E2%86%92%20C)%20%E2%86%92%20D))%20%E2%86%92%20((D%20%E2%86%92%20A)%20%E2%86%92%20(E%20%E2%86%92%20(F%20%E2%86%92%20A))))%0A%0Aopen%20classical%0A%0Avariables%20A%20B%20C%20D%20E%20F:%20Prop%0A%0Aexample:%20((A%20%E2%86%92%20B)%20%E2%86%92%20((false%20%E2%86%92%20C)%20%E2%86%92%20D))%20%E2%86%92%20((D%20%E2%86%92%20A)%20%E2%86%92%20(E%20%E2%86%92%20(F%20%E2%86%92%20A)))%20%20:=%0A%20%20%20%20show%20(((A%20%E2%86%92%20B)%20%E2%86%92%20((false%20%E2%86%92%20C)%20%E2%86%92%20D))%20%E2%86%92%20((D%20%E2%86%92%20A)%20%E2%86%92%20(E%20%E2%86%92%20(F%20%E2%86%92%20A)))),%20from%20%0A%20%20%20%20(%0A%20%20%20%20%20%20%20%20assume%20h1:%20(A%20%E2%86%92%20B)%20%E2%86%92%20((false%20%E2%86%92%20C)%20%E2%86%92%20D),%0A%20%20%20%20%20%20%20%20show%20(D%20%E2%86%92%20A)%20%E2%86%92%20(E%20%E2%86%92%20(F%20%E2%86%92%20A)),%20from%20(%0A%20%20%20%20%20%20%20%20%20%20%20%20assume%20h2:%20(D%20%E2%86%92%20A),%20show%20%20(E%20%E2%86%92%20(F%20%E2%86%92%20A)),%20from%20(%0A%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20assume%20h3:%20E,%20show%20(F%20%E2%86%92%20A),%20from%20(%0A%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20assume%20h4:%20F,%0A%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%0A%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20have%20hfalcd%20:%20(false%20%E2%86%92%20C)%20%E2%86%92%20D,%20from%20(%0A%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20have%20hab%20:%20A%20%E2%86%92%20B,%20from%20(%0A%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20assume%20ha%20:%20A,%0A%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20show%20B,%20from%20sorry%0A%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20),%0A%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20show%20(false%20%E2%86%92%20C)%20%E2%86%92%20D,%20from%20h1%20hab%0A%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20),%0A%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%0A%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20have%20hfalc%20:%20false%20%E2%86%92%20C,%20from%20(%0A%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20assume%20hfal%20:%20false,%0A%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20show%20C,%20from%20by_contradiction%20(%0A%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20assume%20hnc%20:%20%C2%AC%20C,%0A%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20show%20false,%20from%20hfal%0A%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20)%0A%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20),%0A%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%0A%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20have%20hd%20:%20D,%20from%20hfalcd%20hfalc,%0A%0A%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20show%20A,%20from%20h2%20hd%0A%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20%20)%0A%20%20%20%20%20%20%20%20%20%20%20%20)%0A%20%20%20%20%20%20%20%20)%0A%20%20%20%20)%0Aend%0A%0Asection%0A%0A--%20Questao%20386%20dos%20desafios%20:%20((A%20%E2%86%92%20B)%20%E2%88%A7%20(C%20%E2%86%92%20D)),%20((B%20%E2%88%A8%20D)%20%E2%86%92%20E),%20(%C2%ACE)%20%E2%8A%A2%20%C2%AC(A%20%E2%88%A8%20C)%0A%0Avariables%20A%20B%20C%20D%20E:%20Prop%0A%0Aexample%20(h1:%20(A%20%E2%86%92%20B)%20%E2%88%A7%20(C%20%E2%86%92%20D))%20(h2:%20(B%20%E2%88%A8%20D)%20%E2%86%92%20E)%20(h4:%20%C2%ACE%20):%20%C2%AC(A%20%E2%88%A8%20C)%20:=%0A%20%20%20%20show%20%C2%AC(A%20%E2%88%A8%20C),%20from%20%0A%20%20%20%20(assume%20h:%20A%20%E2%88%A8%20C,%20show%20false,%20from%20or.elim%20h%20%0A%20%20%20%20%20%20%20%20(assume%20p1%20:%20A,%20show%20false,%20from%20%0A%20%20%20%20%20%20%20%20%20%20%20%20(have%20p2%20:%20A%20%E2%86%92%20B,%20from%20and.left%20h1,%0A%20%20%20%20%20%20%20%20%20%20%20%20%20have%20p3%20:%20B,%20from%20p2%20p1,%0A%20%20%20%20%20%20%20%20%20%20%20%20%20have%20p4%20:%20B%20%E2%88%A8%20D,%20from%20or.inl%20p3,%0A%20%20%20%20%20%20%20%20%20%20%20%20%20have%20p5%20:%20E,%20from%20h2%20p4,%0A%20%20%20%20%20%20%20%20%20%20%20%20%20show%20false,%20from%20h4%20p5%0A%20%20%20%20%20%20%20%20%20%20%20%20)%0A%20%20%20%20%20%20%20%20)%20%0A%20%20%20%20%20%20%20%20(assume%20p1%20:%20C,%20show%20false,%20from%20%0A%20%20%20%20%20%20%20%20%20%20%20%20(have%20p2%20:%20C%20%E2%86%92%20D,%20from%20and.right%20h1,%0A%20%20%20%20%20%20%20%20%20%20%20%20%20have%20p3%20:%20D,%20from%20p2%20p1,%0A%20%20%20%20%20%20%20%20%20%20%20%20%20have%20p4%20:%20B%20%E2%88%A8%20D,%20from%20or.inr%20p3,%0A%20%20%20%20%20%20%20%20%20%20%20%20%20have%20p5%20:%20E,%20from%20h2%20p4,%0A%20%20%20%20%20%20%20%20%20%20%20%20%20show%20false,%20from%20h4%20p5%0A%20%20%20%20%20%20%20%20%20%20%20%20)%0A%20%20%20%20%20%20%20%20)%0A%20%20%20%20)%0A%0Aend%0A%0A