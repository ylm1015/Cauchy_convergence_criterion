(** MA_CH1 *)

(* 读入库文件 *)
Require Export Real_Axioms.

Parameter R_stru : Real_struct.
Parameter R_axio : Real_axioms R_stru. 

Global Hint Resolve R_axio : core.

Declare Scope MA_R_scope.
Delimit Scope MA_R_scope with ma.
Open Scope MA_R_scope.

Definition ℝ := @R R_stru.
Definition ℕ := @N R_stru.
Definition ℤ := @Z R_stru.
Definition ℚ := @Q R_stru.
Definition fp := @fp R_stru.
Definition zeroR := @zeroR R_stru.
Definition fm := @fm R_stru.
Definition oneR := @oneR R_stru.
Definition Leq := @Leq R_stru.
Definition Abs := @Abs R_stru.

Notation "x + y" := fp[[x, y]] : MA_R_scope.
Notation "0" := zeroR : MA_R_scope.
Notation "x · y" := fm[[x, y]](at level 40) : MA_R_scope.
Notation "1" := oneR : MA_R_scope.
Notation "x ≤ y" := ([x, y] ∈ Leq)(at level 77) : MA_R_scope.
Notation "- a" := (∩(\{ λ u, u ∈ ℝ /\ u + a = 0 \})) : MA_R_scope.
Notation "x - y" := (x + (-y)) : MA_R_scope.
Notation "a ⁻" := (∩(\{ λ u, u ∈ (ℝ ~ [0]) /\ u · a = 1 \}))
  (at level 5) : MA_R_scope.
Notation "m / n" := (m · (n⁻)) : MA_R_scope.
Notation "｜ x ｜" := (Abs[x])(at level 5, x at level 0) : MA_R_scope.

Definition LT x y := x ≤ y /\ x <> y.
Notation "x < y" := (LT x y) : MA_R_scope.
Definition Ensemble_R := @Ensemble_R R_stru R_axio.
Definition PlusR := @PlusR R_stru R_axio.
Definition zero_in_R := @zero_in_R R_stru R_axio.
Definition Plus_P1 := @Plus_P1 R_stru R_axio.
Definition Plus_P2 := @Plus_P2 R_stru R_axio.
Definition Plus_P3 := @Plus_P3 R_stru R_axio.
Definition Plus_P4 := @Plus_P4 R_stru R_axio.
Definition MultR := @MultR R_stru R_axio.
Definition one_in_R := @one_in_R R_stru R_axio.
Definition Mult_P1 := @Mult_P1 R_stru R_axio.
Definition Mult_P2 := @Mult_P2 R_stru R_axio.
Definition Mult_P3 := @Mult_P3 R_stru R_axio.
Definition Mult_P4 := @Mult_P4 R_stru R_axio.
Definition Mult_P5 := @Mult_P5 R_stru R_axio.
Definition LeqR := @LeqR R_stru R_axio.
Definition Leq_P1 := @Leq_P1 R_stru R_axio.
Definition Leq_P2 := @Leq_P2 R_stru R_axio.
Definition Leq_P3 := @Leq_P3 R_stru R_axio.
Definition Leq_P4 := @Leq_P4 R_stru R_axio.
Definition Plus_Leq := @Plus_Leq R_stru R_axio.
Definition Mult_Leq := @Mult_Leq R_stru R_axio.
Definition Completeness := @Completeness R_stru R_axio.

Definition Plus_close := @Plus_close R_stru R_axio.
Definition Mult_close := @Mult_close R_stru R_axio.
Definition one_in_R_Co := @one_in_R_Co R_stru R_axio.
Definition Plus_Co1 := @Plus_Co1 R_stru R_axio.
Definition Plus_Co2 := @Plus_Co2 R_stru R_axio.
Definition Plus_neg1a := @Plus_neg1a R_stru R_axio.
Definition Plus_neg1b := @Plus_neg1b R_stru R_axio.
Definition Plus_neg2 := @Plus_neg2 R_stru R_axio.
Definition Minus_P1 := @Minus_P1 R_stru R_axio.
Definition Minus_P2 := @Minus_P2 R_stru R_axio.
Definition Plus_Co3 := @Plus_Co3 R_stru R_axio.
Definition Mult_Co1 := @Mult_Co1 R_stru R_axio.
Definition Mult_Co2 := @Mult_Co2 R_stru R_axio.
Definition Mult_inv1 := @Mult_inv1 R_stru R_axio.
Definition Mult_inv2 := @Mult_inv2 R_stru R_axio.
Definition Divide_P1 := @Divide_P1 R_stru R_axio.
Definition Divide_P2 := @Divide_P2 R_stru R_axio.
Definition Mult_Co3 := @Mult_Co3 R_stru R_axio.
Definition PlusMult_Co1 := @PlusMult_Co1 R_stru R_axio.
Definition PlusMult_Co2 := @PlusMult_Co2 R_stru R_axio.
Definition PlusMult_Co3 := @PlusMult_Co3 R_stru R_axio.
Definition PlusMult_Co4 := @PlusMult_Co4 R_stru R_axio.
Definition PlusMult_Co5 := @PlusMult_Co5 R_stru R_axio.
Definition PlusMult_Co6 := @PlusMult_Co6 R_stru R_axio.
Definition Order_Co1 := @Order_Co1 R_stru R_axio.
Definition Order_Co2 := @Order_Co2 R_stru R_axio.
Definition OrderPM_Co1 := @OrderPM_Co1 R_stru R_axio.
Definition OrderPM_Co2a := @OrderPM_Co2a R_stru R_axio.
Definition OrderPM_Co2b := @OrderPM_Co2b R_stru R_axio.
Definition OrderPM_Co3 := @OrderPM_Co3 R_stru R_axio.
Definition OrderPM_Co4 := @OrderPM_Co4 R_stru R_axio.
Definition OrderPM_Co5 := @OrderPM_Co5 R_stru R_axio.
Definition OrderPM_Co6 := @OrderPM_Co6 R_stru R_axio.
Definition OrderPM_Co7a := @OrderPM_Co7a R_stru R_axio.
Definition OrderPM_Co7b := @OrderPM_Co7b R_stru R_axio.
Definition OrderPM_Co8a := @OrderPM_Co8a R_stru R_axio.
Definition OrderPM_Co8b := @OrderPM_Co8b R_stru R_axio.
Definition OrderPM_Co9 := @OrderPM_Co9 R_stru R_axio.
Definition OrderPM_Co10 := @OrderPM_Co10 R_stru R_axio.
Definition OrderPM_Co11 := @OrderPM_Co11 R_stru R_axio.
Definition IndSet := @IndSet R_stru.
Definition IndSet_P1 := @IndSet_P1 R_stru.
Definition N_Subset_R := @N_Subset_R R_stru R_axio.
Definition one_in_N := @one_in_N R_stru R_axio.
Definition zero_not_in_N := @zero_not_in_N R_stru R_axio.
Definition IndSet_N := @IndSet_N R_stru R_axio.
Definition MathInd := @MathInd R_stru R_axio.
Definition Nat_P1a := @Nat_P1a R_stru R_axio.
Definition Nat_P2 := @Nat_P2 R_stru R_axio.
Definition Nat_P3 := @Nat_P3 R_stru R_axio.
Definition Nat_P4 := @Nat_P4 R_stru R_axio.
Definition Nat_P5 := @Nat_P5 R_stru R_axio.
Definition Nat_P6 := @Nat_P6 R_stru R_axio.
Definition one_is_min_in_N := @one_is_min_in_N R_stru R_axio.
Definition N_Subset_Z := @N_Subset_Z R_stru.
Definition Z_Subset_R := @Z_Subset_R R_stru R_axio.
Definition Int_P1_Lemma := @Int_P1_Lemma R_stru R_axio.
Definition Int_P1a := @Int_P1a R_stru R_axio.
Definition Int_P1b := @Int_P1b R_stru R_axio.
Definition Int_P2 := @Int_P2 R_stru R_axio.
Definition Int_P3 := @Int_P3 R_stru R_axio.
Definition Int_P4 := @Int_P4 R_stru R_axio.
Definition Int_P5 := @Int_P5 R_stru R_axio.
Definition Z_Subset_Q := @Z_Subset_Q R_stru R_axio.
Definition Q_Subset_R := @Q_Subset_R R_stru R_axio.
Definition Frac_P1 := @Frac_P1 R_stru R_axio.
Definition Frac_P2 := @Frac_P2 R_stru R_axio.
Definition Rat_P1a := @Rat_P1a R_stru R_axio.
Definition Rat_P1b := @Rat_P1b R_stru R_axio.
Definition Rat_P2 := @Rat_P2 R_stru R_axio.
Definition Rat_P3 := @Rat_P3 R_stru R_axio.
Definition Rat_P4 := @Rat_P4 R_stru R_axio.
Definition Rat_P5 := @Rat_P5 R_stru R_axio.
Definition Rat_P6 := @Rat_P6 R_stru R_axio.
Definition Rat_P7 := @Rat_P7 R_stru R_axio.
Definition Rat_P8 := @Rat_P8 R_stru R_axio.
Definition Rat_P9 := @Rat_P9 R_stru R_axio.
Definition Rat_P10 := @Rat_P10 R_stru R_axio.
Definition Even := @Even R_stru.
Definition Odd := @Odd R_stru.
Definition Even_and_Odd_P1 := @Even_and_Odd_P1 R_stru R_axio.
Definition Even_and_Odd_P2_Lemma := @Even_and_Odd_P2_Lemma R_stru R_axio.
Definition Even_and_Odd_P2 := @Even_and_Odd_P2 R_stru R_axio.
Definition Even_and_Odd_P3 := @Even_and_Odd_P3 R_stru R_axio.
Definition Existence_of_irRational_Number :=
  @Existence_of_irRational_Number R_stru R_axio.
Definition Arch_P1 := @Arch_P1 R_stru R_axio.
Definition Arch_P2 := @Arch_P2 R_stru R_axio.
Definition Arch_P3_Lemma := @Arch_P3_Lemma R_stru R_axio.
Definition Arch_P3a := @Arch_P3a R_stru R_axio.
Definition Arch_P3b := @Arch_P3b R_stru R_axio.
Definition Arch_P4 := @Arch_P4 R_stru R_axio.
Definition Arch_P5 := @Arch_P5 R_stru R_axio.
Definition Arch_P6 := @Arch_P6 R_stru R_axio.
Definition Arch_P7 := @Arch_P7 R_stru R_axio.
Definition Arch_P8 := @Arch_P8 R_stru R_axio.
Definition Arch_P9 := @Arch_P9 R_stru R_axio.
Definition Arch_P10 := @Arch_P10 R_stru R_axio.
Definition Abs_is_Function := @Abs_is_Function R_stru R_axio.
Definition Abs_in_R := @Abs_in_R R_stru R_axio.
Definition Distance := @Distance R_stru.
Definition me_zero_Abs := @me_zero_Abs R_stru R_axio.
Definition le_zero_Abs := @le_zero_Abs R_stru R_axio.
Definition Abs_P1 := @Abs_P1 R_stru R_axio.
Definition Abs_P2 := @Abs_P2 R_stru R_axio.
Definition Abs_P3 := @Abs_P3 R_stru R_axio.
Definition Abs_P4 := @Abs_P4 R_stru R_axio.
Definition Abs_P5 := @Abs_P5 R_stru R_axio.
Definition Abs_P6 := @Abs_P6 R_stru R_axio.
Definition Abs_P7 := @Abs_P7 R_stru R_axio.
Definition Abs_P8 := @Abs_P8 R_stru R_axio.

Global Hint Resolve Plus_close zero_in_R Mult_close one_in_R one_in_R_Co
  Plus_neg1a Plus_neg1b Plus_neg2 Minus_P1 Minus_P2
  Mult_inv1 Mult_inv2 Divide_P1 Divide_P2 OrderPM_Co9
  N_Subset_R one_in_N Nat_P1a Nat_P1b
  N_Subset_Z Z_Subset_R Int_P1a Int_P1b
  Z_Subset_Q Q_Subset_R Rat_P1a Rat_P1b Abs_in_R: real.
  
(* 1.2 数集 确界原理 *)

(* 1.2.1 区间与邻域 *)

(* 有限区间 *) 
(* 开区间 *)
Notation "］ a , b ［" := (\{ λ x, x ∈ ℝ /\ a < x /\ x < b \})
  (at level 5, a at level 0, b at level 0) : MA_R_scope.

(* 闭区间 *)
Notation "［ a , b ］" := (\{ λ x, x ∈ ℝ /\ a ≤ x /\ x ≤ b \})
  (at level 5, a at level 0, b at level 0) : MA_R_scope.

(* 左开右闭 *)
Notation "］ a , b ］" := (\{ λ x, x ∈ ℝ /\ a < x /\ x ≤ b \})
  (at level 5, a at level 0, b at level 0) : MA_R_scope.

(* 左闭右开 *)
Notation "［ a , b ［" := (\{ λ x, x ∈ ℝ /\ a ≤ x /\ x < b \})
  (at level 5, a at level 0, b at level 0) : MA_R_scope.

(* 无限区间 *)
Notation "］ a , +∞［" := (\{ λ x, x ∈ ℝ /\ a < x \})
  (at level 5, a at level 0) : MA_R_scope.

Notation "［ a , +∞［" := (\{ λ x, x ∈ ℝ /\ a ≤ x \})
  (at level 5, a at level 0) : MA_R_scope.

Notation "］-∞ , b ］" := (\{ λ x, x ∈ ℝ /\ x ≤ b \})
  (at level 5, b at level 0) : MA_R_scope.

Notation "］-∞ , b ［" := (\{ λ x, x ∈ ℝ /\ x < b \})
  (at level 5, b at level 0) : MA_R_scope.

Notation "]-∞ , +∞[" := ℝ (at level 0) : MA_R_scope.

(* 邻域 *)
Definition Neighbourhood x δ := x ∈ ℝ /\ δ ∈ ℝ /\ x ∈ ］(x - δ),(x + δ)［.

(* 邻域 *)
Definition Neighbor a δ := \{ λ x, x ∈ ℝ /\ ｜ (x - a) ｜ < δ \}.
Notation "U( a ; δ )" := (Neighbor a δ)
  (a at level 0, δ at level 0, at level 4) : MA_R_scope.

(* 左邻域 *)
Definition leftNeighbor a δ := ］a-δ, a］.

(* 右邻域 *)
Definition rightNeighbor a δ := ［a, (a+δ)［.

(* 去心邻域 *)
Definition Neighbor0 a δ := \{ λ x, x ∈ ℝ 
  /\ 0 < ｜(x-a)｜ /\ ｜(x-a)｜ < δ \}.
Notation "Uº( a ; δ )" := (Neighbor0 a δ)
  (a at level 0, δ at level 0, at level 4) : MA_R_scope.

(* 左去心邻域 *)
Definition leftNeighbor0 a δ := ］a-δ, a［.
Notation "U-º( a ; δ )" := (leftNeighbor0 a δ)
  (a at level 0, δ at level 0, at level 4) : MA_R_scope.

(* 右去心邻域 *)
Definition rightNeighbor0 a δ := ］a, (a+δ)［.
Notation "U+º( a ; δ )" := (rightNeighbor0 a δ)
  (a at level 0, δ at level 0, at level 4) : MA_R_scope.

(* 无穷邻域 *)
Definition Neighbor_infinity M := \{ λ x, x ∈ ℝ /\ M ∈ ℝ
  /\ 0 < M /\ M < ｜x｜ \}.
Notation "U(∞) M" := (Neighbor_infinity M) (at level 5) : MA_R_scope.

(* 正无穷邻域 *)
Definition PNeighbor_infinity M := \{ λ x, x ∈ ℝ /\ M ∈ ℝ /\ M < x \}.
Notation "U(+∞) M" := (［ M , +∞［) (at level 5) : MA_R_scope.

(* 负无穷邻域 *)
Definition NNeighbor_infinity M := \{ λ x, x ∈ ℝ /\ M ∈ ℝ /\ x < M \}.
Notation "U(-∞) M" := (］-∞ , M ［) (at level 5) : MA_R_scope.

(* 1.2.2 有界集 确界原理 *)

(* 上界 *)
Definition UpperBound S M := S ⊂ ℝ /\ M ∈ ℝ /\ (∀ x, x ∈ S -> x ≤ M).

(* 下界 *)
Definition LowerBound S L := S ⊂ ℝ /\ L ∈ ℝ /\ (∀ x, x ∈ S -> L ≤ x).

(* 有界集 *)
Definition Bounded S := ∃ M L, UpperBound S M /\ LowerBound S L.

(* 无界集 *)
Definition Unbounded S := ~ (Bounded S).

(* 上确界 *)
Definition Sup S η := UpperBound S η /\ (∀ α, α ∈ ℝ -> α < η
  -> (∃ x0, x0 ∈ S /\ α < x0)).

(* 下确界 *)
Definition Inf S ξ := LowerBound S ξ /\ (∀ β, β ∈ ℝ -> ξ < β
  -> (∃ x0, x0 ∈ S /\ x0 < β)).
  
Definition Max S c := S ⊂ ℝ /\ c ∈ S /\ (∀ x, x ∈ S -> x ≤ c).

Definition Min S c := S ⊂ ℝ /\ c ∈ S /\ (∀ x, x ∈ S -> c ≤ x).

Corollary Max_Corollary : ∀ S c1 c2, Max S c1 -> Max S c2 -> c1 = c2.
Proof.
  intros. unfold Max in *. destruct H as [H []], H0 as [H0 []].
  pose proof H1. pose proof H3. apply H2 in H6. apply H4 in H5.
  apply Leq_P2; auto.
Qed.
  
Corollary Min_Corollary : ∀ S c1 c2, Min S c1 -> Min S c2 -> c1 = c2.
Proof.
  intros. unfold Min in *. destruct H as [H []], H0 as [H0 []].
  pose proof H1. pose proof H3. apply H2 in H6. apply H4 in H5.
  apply Leq_P2; auto.
Qed.

Definition Sup_Equal S η := Min \{ λ u, UpperBound S u \} η.

Corollary Sup_Corollary : ∀ S η, Sup S η <-> Sup_Equal S η.
Proof.
  intros. split; intro.
  - red in H; red. destruct H, H as [H []]. repeat split. 
    unfold Included; intros. apply AxiomII in H3 as [_[_[]]]; auto.
    apply AxiomII; split. unfold Ensemble; exists ℝ; auto. split; auto.
    intros. apply AxiomII in H3 as [H3 [H4 []]]. pose proof H5.
    apply (Order_Co1 x η) in H7 as [H7 | [|]]; auto.
    + apply H0 in H7 as [x0 []]; auto. pose proof H7. apply H6 in H9.
      destruct H8. elim H10. apply Leq_P2; auto.
    + destruct H7. auto.
    + rewrite H7. apply Leq_P1; auto.
  - red in H; red. destruct H as [H []]. apply AxiomII in H0 as [_[H0 []]].
    repeat split; auto. intros. apply NNPP; intro.
    assert (∀ x1, x1 ∈ S -> x1 ≤ α).
    { intros. apply NNPP; intro. elim H6. exists x1. split; auto.  
      pose proof H4. apply (@ Order_Co1 x1 α) in H9
      as [H9 | [|]]; auto. elim H8. destruct H9. auto. 
      rewrite H9 in H8. elim H8. apply Leq_P1; auto. }
    assert (α ∈ \{ λ u, UpperBound S u \}).
    { apply AxiomII. split. exists ℝ; auto. split; auto. }
    apply H1 in H8. destruct H5. elim H9. 
    apply Leq_P2; auto.
Qed.

Definition Inf_Equal S ξ := Max \{ λ u, LowerBound S u \} ξ.

Corollary Inf_Corollary : ∀ S ξ, Inf S ξ <-> Inf_Equal S ξ.
Proof.
  intros. split; intro.
  - red in H; red. destruct H, H as [H []]. repeat split.
    unfold Included; intros. apply AxiomII in H3 as [_[_[]]]; auto.
    apply AxiomII; split. exists ℝ; auto. repeat split; auto.
    intros. apply AxiomII in H3 as [H3 [H4 []]]. pose proof H5.
    apply (@ Order_Co1 x ξ) in H7 as [H7 | [|]]; auto.
    + destruct H7. auto.
    + apply H0 in H7 as [x0 []]; auto. pose proof H7. apply H6 in H9.
      destruct H8. elim H10. apply Leq_P2; auto.
    + rewrite H7. apply Leq_P1; auto.
  - red in H; red. destruct H as [H []]. apply AxiomII in H0 as [_[H2 []]].
    repeat split; auto. intros. apply NNPP; intro.
    assert (∀x1, x1 ∈ S -> β ≤ x1).
    { intros. apply NNPP; intro. elim H6. exists x1. split; auto.
      pose proof H4. apply (Order_Co1 x1 β) in H9 
      as [H9 | [|]]; auto. elim H8. destruct H9. auto.
      rewrite H9 in H8. elim H8. apply Leq_P1; auto. }
    assert (β ∈ \{ λ u, LowerBound S u \}).
    { apply AxiomII; split. exists ℝ; auto. repeat split; auto. }
    apply H1 in H8. destruct H5. elim H9.
    apply Leq_P2; auto.
Qed.

(* 确界原理 *)

(* Theorem SupL' : ∀ S, S ⊂ ℝ -> S <> Φ -> (∃ M, UpperBound S M)
  -> exists η, Sup S η.
Proof.
  intros. destruct H1 as [M].
  set (Y := \{ λ u, UpperBound S u \}).
  assert (Y <> Φ).
  { apply NEexE. exists M. apply AxiomII; split; auto. 
    red in H1. destruct H1 as [_[]]. eauto. }
  assert (Y ⊂ ℝ).
  { unfold Included. intros. apply AxiomII in H3. 
    destruct H3 as [_[_[]]]. auto. }
  assert (∃ c, c ∈ ℝ /\ (∀ x y, x ∈ S -> y ∈ Y -> (x ≤ c /\ c ≤ y))).
  { apply (@ Completeness R_stru); auto. intros. apply AxiomII in H5
    as [_[_[]]]. auto. }
  destruct H4 as [c[]]. unfold Sup. exists c. split.
  - unfold UpperBound. repeat split; auto; intros.
    apply NEexE in H2 as [y]. apply (H5 x y); auto.
  - intros. apply NNPP. intro.
    assert (∀ x0, x0 ∈ S -> x0 ≤ α).
    { intros. apply NNPP; intro. apply H8. exists x0.
      split; auto. apply (@ Order_Co1 R_stru R_axio α x0) in H6 
      as [H6|[]]; auto. destruct H6. contradiction. rewrite H6 in H10.
      elim H10. apply (@ Leq_P1 R_stru); auto. }
    assert (α ∈ Y).
    { apply AxiomII; split; eauto. repeat split; intros; auto. }
    apply NEexE in H0 as []. apply (H5 x α) in H10 as []; auto.
    destruct H7. apply H12. apply (@ Leq_P2 R_stru); auto.
Qed. *)

(* 上确界引理 *)
Lemma SupLemma : ∀ X, X ⊂ ℝ -> X <> Φ -> (∃ c, UpperBound X c) 
  -> exists ! η, Sup X η.
Proof.
  intros. set (Y:=\{ λ u, UpperBound X u \}).
  assert (Y <> Φ).
  { apply NEexE. destruct H1 as [x]. exists x. apply AxiomII;
    split; auto. destruct H1 as [_[]]. unfold Ensemble. exists ℝ; auto. }
  assert (Y ⊂ ℝ).
  { unfold Included; intros. apply AxiomII in H3 as [_].
    destruct H3 as [_[]]. auto. }
  assert (∃ c, c ∈ ℝ /\ (∀ x y, x ∈ X -> y ∈ Y 
    -> (x ≤ c /\ c ≤ y))) as [c[]].
  { apply Completeness; auto. intros. apply AxiomII in H5 as [_].
    destruct H5 as [_[]]. apply H6 in H4; auto. }
  assert (c ∈ Y).
  { apply AxiomII; repeat split; eauto. intros.
    apply NEexE in H2 as [y]. pose proof H5 _ _ H6 H2; tauto. }
  assert (Min \{ λ u, UpperBound X u \} c).
  { red. repeat split; auto. intros y H7. apply NEexE in H0 as [x].
    pose proof H5 _ _ H0 H7. tauto. }
  exists c. split. apply Sup_Corollary. auto. intros.
  apply Sup_Corollary in H8. apply (Min_Corollary Y); auto.
Qed.

(* 下确界引理 *)
Lemma InfLemma : ∀ X, X ⊂ ℝ -> X <> Φ -> (∃ c, LowerBound X c)
  -> exists ! ξ, Inf X ξ.
Proof.
  intros. set(Y:=\{ λ u, LowerBound X u \}).
  assert (Y <> Φ).
  { apply NEexE. destruct H1 as [x]. exists x. apply AxiomII;
    split; auto. destruct H1 as [_[]]. exists ℝ; auto. }
  assert (Y ⊂ ℝ).
  { unfold Included. intros. apply AxiomII in H3 as [].
    destruct H4 as [_[]]; auto. }
  assert (∃ c, c ∈ ℝ /\ (∀ y x, y ∈ Y -> x ∈ X 
    -> y ≤ c /\ c ≤ x)) as [c[]].
  { apply Completeness; auto. intros.
    apply AxiomII in H4 as [_[_[]]]. apply H6 in H5; auto. }
  assert (c ∈ Y).
  { apply AxiomII. repeat split; eauto. intros. 
    apply NEexE in H2 as [y]. pose proof H5 _ _ H2 H6; tauto. }
  assert (Max \{ λ u, LowerBound X u \} c).
  { red. repeat split; auto. intros y H7. apply NEexE in H0 as [x].
    pose proof H5 _ _ H7 H0; tauto. }
  exists c. split. apply Inf_Corollary; auto. intros.
  apply Inf_Corollary in H8. apply (Max_Corollary Y); auto.
Qed.

(* 确界原理 *)
Theorem Sup_Inf_Principle : ∀ X, X ⊂ ℝ -> X <> Φ
  -> ((∃ c, UpperBound X c) -> exists ! η, Sup X η)
  /\ ((∃ c, LowerBound X c) -> exists ! ξ, Inf X ξ).
Proof.
  intros. split; intros.
  - apply SupLemma; auto.
  - apply InfLemma; auto.
Qed.

(* 1.3 函数概念 *)

(* 1.3.1 函数的定义 *)
(* Note ：MK中已经给出 *)

(* 有序数对 *)
(* Definition Ordered x y := [ [x] | [x|y] ].
Notation "[ x , y ]" := (Ordered x y) (at level 0) : MA_R_scope. *)

(* 以有序数对的第一个元为第一坐标 *)
(* Definition First z := ∩∩z. *)

(* 以有序数对的第二个元为第二坐标 *)
(* Definition Second z := (∩∪z)∪(∪∪z) ~ (∪∩z). *)

(* 有序数对相等，对应坐标相等 *)
(* Theorem ProdEqual : ∀ x y u v, Ensemble x -> Ensemble y
  -> ([x, y] = [u, v] <-> x = u /\ y = v).
Proof.
  split; intros; [|destruct H1; subst; auto].
  assert (Ensemble ([x,y])); auto. rewrite H1 in H2.
  apply MKT49b in H2 as [].
  rewrite <-(MKT54a x y), H1,
  <-(MKT54b x y),H1,MKT54a,MKT54b; auto.
Qed. *)

(* 关系 *)
(* Definition Relation r := ∀ z, z ∈ r -> (∃ x y, z = [x, y]). *)

(* 关系的复合及关系的逆 *)
(* Definition Composition r s := \{\ λ x z, ∃ y, [x,y] ∈ s /\ [y,z] ∈ r \}\.
Notation "r ∘ s" := (Composition r s) (at level 50).

Definition Inverse r := \{\ λ x y, [y, x] ∈ r \}\.
Notation "r ⁻¹" := (Inverse r) (at level 5). *)

(* 满足性质P的有序数对构成的集合: { (x,y) : ... } *)
(* Notation "\{\ P \}\" :=
  (\{ λ z, ∃ x y, z = [x,y] /\ P x y \}) (at level 0). *)

(* 分类公理图示II关于有序数对的适应性事实 *)
(* Fact AxiomII' : ∀ a b P,
  [a,b] ∈ \{\ P \}\ <-> Ensemble ([a,b]) /\ (P a b).
Proof.
  split; intros.
  - PP H x y. apply MKT55 in H0 as []; subst; auto; ope.
  - destruct H. appA2G.
Qed. *)

(* 函数 *)
(* Definition Function f := 
  Relation f /\ (∀ x y z, [x,y] ∈ f -> [x,z] ∈ f -> y = z). *)

(* 定义域 *)
(* Definition Domain f := \{ λ x, ∃ y, [x,y] ∈ f \}.
Notation "dom( f )" := (Domain f) (at level 5). *)

(* 值域 *)
(* Definition Range f := \{ λ y, ∃ x, [x,y] ∈ f \}.
Notation "ran( f )" := (Range f) (at level 5). *)

(* f在点x的函数值 *)
(* Definition Value f x := ∩\{ λ y, [x,y] ∈ f \}.
Notation "f [ x ]" := (Value f x) (at level 5). *)

(* 声明函数的定义域和值域都是实数ℝ类型 *)
(* Definition Function f : Prop := dom(f) = ℝ /\ ran(f) ⊂ ℝ. *)

(* 1.3.2 函数的四则运算 *)

Definition Plus_Fun f g :=
  \{\ λ x y, x ∈ dom(f) /\ x ∈ dom(g) /\ y = f[x] + g[x] \}\.
Definition Sub_Fun f g :=
  \{\ λ x y, x ∈ dom(f) /\ x ∈ dom(g) /\ y = f[x] - g[x] \}\.
Definition Mult_Fun f g :=
  \{\ λ x y, x ∈ dom(f) /\ x ∈ dom(g) /\ y = f[x] · g[x] \}\.
Definition Div_Fun f g :=
  \{\ λ x y, x ∈ dom(f) /\ x ∈ dom(g) /\ g[x] <> 0 /\ y = f[x] / g[x] \}\.
  
Notation "f \+ g" := (Plus_Fun f g) (at level 45, left associativity).
Notation "f \- g" := (Sub_Fun f g) (at level 45, left associativity).
Notation "f \· g" := (Mult_Fun f g) (at level 40, left associativity).
Notation "f // g" := (Div_Fun f g) (at level 40, left associativity).

(* 1.3.3 复合函数 *)

Definition Comp : ∀ f g, Function f -> Function g -> Function (f ∘ g).
Proof.
  split; intros; unfold Composition; auto.
  appoA2H H1. appoA2H H2. rdeHex. destruct H0.
  apply H with x0; auto. rewrite (H7 x x0 x1); auto.
Qed.

(* 复合函数完整条件定义 *)
(* Definition Comp f g := ∀ f g x u, Function f -> Function g
  -> x ∈ dom(g) /\ g[x] ∈ dom(f)
  /\ u = g[x] /\ (f ∘ g)[x] = f[u] /\ dom(f ∘ g) = 
  (\{ λ x, g[x] ∈ dom(f) \} ∩ dom(g)) /\ dom(f ∘ g) <> Φ. *)

(* Definition Comp (f g : Fun) := ∀(f g : Fun) (x u : R), x ∈ dom[g] /\
g[x] ∈ dom[f] /\ u = g[x] /\ (f ∘ g) [x] = f[u]/\ dom[(f ∘ g)] =
(\{ λ x : R, (g [x] ∈ dom[f]) \} ∩ dom[g]) /\ NotEmpty dom[(f ∘ g)]. *)

(* 1.3.4 反函数 *)

Definition Inverse_Fun f g := Function1_1 f /\ g = f⁻¹.

Corollary Inverse_Co1 : ∀ f u, Function f -> Function f⁻¹ -> u ∈ dom(f)
  -> (f⁻¹)[f[u]] = u.
Proof.
  intros. apply Property_Value,invp1,Property_Fun in H1; auto.
Qed.

Corollary Inverse_Co2: ∀ f u, Function f -> Function f⁻¹ -> u ∈ ran(f)
  -> f[(f⁻¹)[u]] = u.
Proof.
  intros. rewrite reqdi in H1. apply Property_Value in H1; auto.
  apply ->invp1 in H1; auto. apply Property_Fun in H1; auto.
Qed.

(* 1.4 具有某些特性的函数 *)

(* 1.4.1 有界函数 *)

Definition UpBoundedFun f D : Prop :=
  Function f /\ D = dom(f) /\ (∃ M, M ∈ ℝ /\ ∀ x, x ∈ D -> f[x] ≤ M).

Definition LowBoundedFun f D : Prop :=
  Function f /\ D = dom(f) /\ (∃ L, L ∈ ℝ /\ ∀ x, x ∈ D -> L ≤ f[x]).

Definition BoundedFun f D : Prop := Function f /\ D = dom(f) 
  /\ (∃ M, M ∈ ℝ -> 0 < M /\ ∀ x, x ∈ D -> ｜[f[x]]｜ ≤ M).

(* 1.4.2 单调函数 *)

Definition IncreaseFun f := Function f
  /\ (∀ x1 x2, x1 ∈ dom(f) -> x2 ∈ dom(f) -> x1 < x2 -> f[x1] ≤ f[x2]).
Definition StrictIncreaseFun f := Function f
  /\ (∀ x1 x2, x1 ∈ dom(f) -> x2 ∈ dom(f) -> x1 < x2 -> f[x1] < f[x2]).
Definition DecreaseFun f := Function f
  /\ (∀ x1 x2, x1 ∈ dom(f) -> x2 ∈ dom(f) -> x1 < x2 -> f[x2] ≤ f[x2]).
Definition StrictDecreaseFun f := Function f
  /\ (∀ x1 x2, x1 ∈ dom(f) -> x2 ∈ dom(f) -> x1 < x2 -> f[x2] < f[x1]).

Theorem Theorem1_2_1 : ∀ f, Function f -> dom(f) ⊂ ℝ -> ran(f) ⊂ ℝ
  -> StrictIncreaseFun f -> StrictIncreaseFun f⁻¹.
Proof.
  intros; unfold StrictIncreaseFun in *. destruct H2 as [H2 H3].
  assert (Function f⁻¹).
  { unfold Function in *. unfold Relation in *. destruct H as []; split.
    - intros. apply AxiomII in H5 as [H5 [x[y]]]. exists x, y; tauto.
    - intros. apply AxiomII' in H5 as []; apply AxiomII' in H6 as [].
      assert (y ∈ ℝ).
      { unfold Included in H0. apply H0. apply AxiomII; split.
        apply MKT49c2 in H5; auto. exists x; auto. }
      assert (z ∈ ℝ).
      { apply H0. apply Property_dom in H8; auto. }
      New H7. New H8. apply Property_dom in H11, H12; auto.
      destruct (Order_Co1 y z) as [H13 | [|]]; auto.
      + apply H3 in H13; auto.
        assert (x = f[y] /\ x = f[z]) as [].
        { split; [apply (H4 y)|apply (H4 z)]; auto;
          apply Property_Value; auto. }
        rewrite <-H14, <-H15 in H13. destruct H13. elim H16. auto.
      + apply H3 in H13; auto.
        assert (x = f[y] /\ x = f[z]) as [].
        { split; [apply (H4 y)|apply (H4 z)]; auto;
          apply Property_Value; auto. }
        rewrite <-H14, <-H15 in H13. destruct H13. elim H16. auto. }
  split; auto; intros.
  - New H5; New H6. apply Property_Value,Property_ran in H8, H9; auto.
    rewrite <-deqri in H8, H9.
    destruct (Order_Co1 (f⁻¹)[x1] (f⁻¹)[x2])
    as [H10 | [|]]; auto.
    + apply H3 in H10; auto. rewrite f11vi in H10, H10; auto;
      try rewrite reqdi; auto. destruct H7, H10. elim H12.
      rewrite <-reqdi in H5, H6. apply Leq_P2; auto.
    + assert (f[(f ⁻¹)[x1]] = f[(f ⁻¹)[x2]]). { rewrite H10. auto. }
      rewrite <-reqdi in H5, H6. rewrite f11vi in H11, H11; auto.
      destruct H7. elim H12; auto.
Qed.

Theorem Theorem1_2_2 : ∀ f, Function f -> dom(f) ⊂ ℝ -> ran(f) ⊂ ℝ 
  -> StrictDecreaseFun f -> StrictDecreaseFun f⁻¹.
Proof.
  intros. unfold StrictDecreaseFun in *. destruct H2 as [].
  assert (Function f⁻¹).
  { unfold Function in *. unfold Relation in *. destruct H as []; split.
    + intros. apply AxiomII in H5 as [H5 [x[y]]]. exists x, y; tauto.
    + intros. apply AxiomII' in H5 as [], H6 as [].
      New H7; New H8. apply Property_dom in H9, H10.
      destruct (Order_Co1 y z) as [H11 | [|]]; auto.
      * apply H3 in H11; auto.
        assert (x = f[z] /\ x = f[y]) as [].
        { split; [apply (H4 z)|apply (H4 y)]; auto;
          apply Property_Value; auto. }
        rewrite <-H12, <-H13 in H11. destruct H11. elim H14. auto.
      * apply H3 in H11; auto.
        assert (x = f[z] /\ x = f[y]) as [].
        { split; [apply (H4 z)|apply (H4 y)]; auto;
          apply Property_Value; auto. }
        rewrite <-H12, <-H13 in H11. destruct H11. elim H14. auto. }
  split; auto; intros.
  - New H5; New H6. apply Property_Value,Property_ran in H8, H9; auto.
    rewrite <-deqri in H8, H9.
    destruct (Order_Co1 (f⁻¹)[x2] (f⁻¹)[x1]) 
    as [H10 | [|]]; auto.
    + apply H3 in H10; auto. rewrite f11vi in H10, H10; auto;
      rewrite <-reqdi in H5, H6; auto. destruct H7, H10. elim H11.
      apply Leq_P2; auto.
    + assert (f[(f ⁻¹)[x2]] = f[(f ⁻¹)[x1]]). { rewrite H10. auto. }
      rewrite <-reqdi in H5, H6. rewrite f11vi in H11, H11; auto.
      destruct H7. elim H12; auto.
Qed.

(* 1.4.3 奇函数和偶函数 *)

(* 奇函数 *)
Definition OddFun f := Function f /\ dom(f) ⊂ ℝ /\ ran(f) ⊂ ℝ
  /\ (∀ x, x ∈ dom(f) -> f[-x] = -f[x]).

(* 偶函数 *)
Definition EvenFun f := Function f /\ dom(f) ⊂ ℝ /\ ran(f) ⊂ ℝ
  /\ (∀ x, x ∈ dom(f) -> f[-x] = f[x]).

(* 1.4.4 周期函数 *)
Definition PeriodicFun f := Function f /\ (∃ σ, σ ∈ ℝ -> 0 < σ 
  /\ (∀ x, x ∈ ℝ -> x ∈ dom(f) -> (x + σ ∈ dom(f) -> f[x + σ] = f[x])
  /\ (x - σ ∈ dom(f) -> f[x - σ] = f[x]))).

(* ℂ ℕ ℝ ℚ ℤ *)
(* 2 数列极限 *)

(* 2.1 数列极限 *)

(* 定义：数列 *)
Definition IsSeq f := Function f /\ dom(f) = ℕ /\ ran(f) ⊂ ℝ.

(* 定义1：数列极限 *)
Definition Limit_Seq x a := IsSeq x /\ (∀ ε, ε ∈ ℝ /\ 0 < ε
  -> (∃ N, N ∈ ℕ /\ (∀ n, n ∈ ℕ -> N < n -> Abs[x[n] - a] < ε))).

(* 定义1' 数列极限的邻域刻画 *)
Definition Limit_Seq' x a := IsSeq x /\ (∀ ε, ε ∈ ℝ /\ 0 < ε
  -> Finite \{ λ u, u ∈ ℕ /\ x[u] ∉ (Neighbor a ε) \}).

Theorem MathInd_Ma : ∀ E, E ⊂ ℕ -> 1 ∈ E
  -> (∀ x, x ∈ E -> (x + 1) ∈ E) -> E = ℕ.
Proof.
  intros. assert (IndSet E).
  { split; auto. unfold Included; intros. apply N_Subset_R; auto. }
  apply MKT27; split; auto. unfold Included; intros.
  apply AxiomII in H3 as []. apply H4. apply AxiomII; split; auto.
  apply (MKT33 ℕ); auto. apply (MKT33 ℝ).
  apply Ensemble_R; auto. apply N_Subset_R; auto.
Qed.

Corollary Nat_nle_gt : ∀ n m, n ∈ ℕ -> m ∈ ℕ -> ~ (n ≤ m) <-> (m < n).
Proof.
  intros. apply N_Subset_R in H, H0. split; intros.
  - apply NNPP; intro. destruct (Leq_P4 m n); auto.
    destruct (classic (m = n)).
    + elim H1. rewrite H4. apply Leq_P1; auto.
    + elim H2. split; auto.
  - destruct H1. intro. elim H2. apply Leq_P2; auto.
Qed.

Corollary Nat_le_ngt : ∀ n m, n ∈ ℕ -> m ∈ ℕ -> n ≤ m <-> ~ (m < n).
Proof.
  intros. apply N_Subset_R in H, H0. split; intros.
  - intro. destruct H2. elim H3. apply Leq_P2; auto.
  - apply NNPP; intro. destruct (Leq_P4 m n); auto.
    destruct (classic (m = n)).
    + elim H2; rewrite H4; apply Leq_P1; auto.
    + elim H1; split; auto.
Qed.

Corollary Nat_P4a: ∀ m n, m ∈ ℕ -> n ∈ ℕ -> (n + 1) ≤ m -> n < m.
Proof.
  intros. apply N_Subset_R in H as Ha, H0 as Hb.
  assert (n < n + 1).
  { apply (Leq_P1 n) in Hb as Hc. destruct OrderPM_Co9.
    apply (OrderPM_Co3 _ _ 0 1) in Hc; auto with real.
    rewrite Plus_P1 in Hc; auto. split; auto. intro.
    assert (n - n = n + 1 - n). { rewrite <-H4; auto. }
    rewrite Minus_P1, (Plus_P4 n), <-Plus_P3, Plus_neg2, Plus_P1 in H5;
    auto with real. }
  destruct H2. split.
  - apply (Leq_P3 _ (n + 1) _); auto with real.
  - intro. rewrite <-H4 in H1. elim H3. apply Leq_P2; auto with real.
Qed.

Corollary Nat_P4b : ∀ m n, m ∈ ℕ -> n ∈ ℕ -> n ≤ m -> n < m + 1.
Proof.
  intros. apply N_Subset_R in H as Ha, H0 as Hb.
  assert (m < m + 1).
  { apply (Leq_P1 m) in Ha as Hc. destruct OrderPM_Co9.
    apply (OrderPM_Co3 _ _ 0 1) in Hc; auto with real.
    rewrite Plus_P1 in Hc; auto. split; auto. intro.
    assert (m - m = m + 1 - m). { rewrite <-H4; auto. }
    rewrite Minus_P1, (Plus_P4 m), <-Plus_P3, Plus_neg2, Plus_P1 in H5;
    auto with real. }
  destruct H2. split.
  - apply (Leq_P3 _ m _); auto with real.
  - intro. rewrite H4 in H1. elim H3. apply Leq_P2; auto with real.
Qed.

(* 小于等于某个数的自然数集为非空有限集 *)
Theorem NatFinite : ∀ n, n ∈ ℕ -> Finite \{ λ u, u ∈ ℕ /\ u ≤ n \}
  /\ \{ λ u, u ∈ ℕ /\ u ≤ n \} <> Φ.
Proof.
  intros. split.
  - set (F := \{ λ u, u ∈ ℕ /\ Finite \{ λ v, v ∈ ℕ /\ v ≤ u \} \}).
    assert (F = ℕ).
    { apply MathInd_Ma; auto; unfold Included; intros.
      apply AxiomII in H0 as [_[]]; auto.
      - apply AxiomII; repeat split; eauto with real.
        assert (\{ λ v, v ∈ ℕ /\ v ≤ 1 \} = [1]).
        { apply AxiomI; split; intros.
          - apply AxiomII in H0 as [H0 []]. apply MKT41; eauto with real.
            apply Leq_P2; auto with real.
            apply NNPP; intro. destruct (classic (z = 1)).
            + elim H3. rewrite H4. apply Leq_P1; auto with real.
            + destruct one_is_min_in_N as [H5 []]. pose proof H1.
              apply H7 in H8. elim H4. apply Leq_P2; auto with real.
          - apply MKT41 in H0; eauto with real. rewrite H0.
            apply AxiomII; repeat split; eauto with real. 
            apply Leq_P1; apply one_in_R_Co. }
        rewrite H0. apply finsin; eauto with real.
      - apply AxiomII in H0 as [H0 []]. pose proof IndSet_N as Ha. 
        apply AxiomII; repeat split; eauto with real.
        assert (\{ λ v, v ∈ ℕ /\ v ≤ x + 1 \} 
          = \{ λ v, v ∈ ℕ /\ v ≤ x \} ∪ [x + 1]).
          { apply AxiomI; split; intros.
            - apply AxiomII in H3 as [H3 []]. apply MKT4.
              destruct (classic (z = x + 1)).
              + right. apply MKT41; eauto with real.
              + left. apply AxiomII; repeat split; auto.
                assert (z < x + 1). split; auto.
                apply Nat_P4 in H7; auto with real.
                apply Plus_Leq with (z:=-(1)) in H7; auto with real.
                rewrite <-Plus_P3, <-Plus_P3 in H7; auto with real.
                rewrite Minus_P1, Minus_P1 in H7; auto with real.
                rewrite Plus_P1, Plus_P1 in H7; auto with real.
            - apply MKT4 in H3 as [].
              + apply AxiomII in H3 as [H3 []].
                apply AxiomII; repeat split; auto.
                assert (z + 0 ≤ x + 1).
                { apply OrderPM_Co3; try apply OrderPM_Co9; auto with real. }
                rewrite Plus_P1 in H6; auto with real.
              + apply MKT41 in H3; eauto with real. rewrite H3.
                apply AxiomII; repeat split; eauto with real.
                apply Leq_P1; auto with real. }
          rewrite H3. apply MKT168; auto. apply finsin; eauto with real. }
    rewrite <-H0 in H. apply AxiomII in H as [H []]; auto.
  - apply NEexE. exists 1. apply AxiomII; repeat split; eauto with real.
    pose proof one_is_min_in_N. destruct H0 as [H0 []]. apply H2; auto.
Qed.

(* 最大值 *)
Definition maxR A r := A ⊂ ℝ /\ r ∈ A /\ (∀ x, x ∈ A -> x ≤ r).

(* 非空有限的实数集有最大值 (非空有限的自然数集有最大值易证: 自然数集是实数集的子集) *)
Theorem finite_maxR : ∀ A, A <> Φ -> Finite A -> A ⊂ ℝ
  -> (∃ r, maxR A r).
Admitted.

(* 非空有限的自然数集有最大值 *)
Theorem finite_maxN : ∀ A, A <> Φ -> Finite A -> A ⊂ ℕ
  -> (∃ r, maxR A r).
Proof.
  intros. assert (A ⊂ ℝ).
  { unfold Included; intros; apply N_Subset_R; auto. }
  apply finite_maxR; auto.
Qed.

(* 两种极限定义等价 *)
Theorem Limit_Equal : ∀ x a, IsSeq x -> a ∈ ℝ 
  -> Limit_Seq x a <-> Limit_Seq' x a.
Proof.
  intros. unfold Limit_Seq; unfold Limit_Seq'. split; intros.
  - destruct H1 as [Ha H1]. split; auto. intros.
    apply H1 in H2 as H3. destruct H3 as [N []].
    (* set写法 *)
    assert (∀ n, n ∈ ℕ -> ∃ A, A = \{ λ u, u ∈ ℕ /\ u ≤ n \}).
    { intros. exists \{ λ u, u ∈ ℕ /\ u ≤ n \}. auto. }
    New H3. apply H5 in H3. destruct H3 as [A].
    assert (\{ λ u, u ∈ ℕ /\ x[u] ∉ (Neighbor a ε) \} ⊂ A).
    { intros z H7. apply AxiomII in H7 as [H8 []]. rewrite H3.
      apply AxiomII; repeat split; auto. apply NNPP; intro.
      apply Nat_nle_gt in H10; auto. apply H4 in H10; auto.
      elim H9. destruct Ha as [Ha []].
      assert (x[z] ∈ ran(x)).
      { apply Property_dm; auto. rewrite H11; auto. }
      destruct H10. apply AxiomII; repeat split; eauto. }
    apply @ finsub with (A:= A); auto. rewrite H3. apply NatFinite; auto.
  - destruct H1 as [Ha H1]. split; auto.
    intros ε H2. pose proof H2 as Hb. 
    apply H1 in H2. apply finite_maxN in H2.
    destruct H2 as [N [H2 []]]. apply AxiomII in H3 as [H3 []].
    exists N; split; auto. intros. apply NNPP; intro.
    assert (n ∈ \{ λ u, u ∈ ℕ /\ x[u] ∉ U(a;ε) \}).
    { apply AxiomII; repeat split; eauto. 
      intro. apply AxiomII in H10 as [H10 []]. contradiction. }
    apply H4 in H10. apply Nat_le_ngt in H10; auto.
    * apply NEexE. admit.
Admitted.

(* 收敛数列 *)
Definition Convergence x := ∃ a, a ∈ ℝ /\ Limit_Seq x a.

(* 发散数列 *)
Definition Divergence x := IsSeq x /\ (∀ a, a ∈ ℝ /\ ~ Limit_Seq x a).

(* 定义2：无穷小数列 *)
Definition Infinitesimal x := Limit_Seq x 0.

(* 定理2.1 *)
Theorem Theorem2_1 : ∀ x a, a ∈ ℝ -> IsSeq x -> Limit_Seq x a  
  <-> Infinitesimal \{\ λ u v, u ∈ ℕ /\ v ∈ ℝ /\ v = x[u] - a \}\.
Proof.
  split; intros.
  - unfold Infinitesimal. unfold Limit_Seq in *. destruct H1 as [H1 H2].
    assert (IsSeq \{\ λ u v, u ∈ ℕ /\ v ∈ ℝ /\ v = x[u] - a \}\).
    { unfold IsSeq in *. destruct H1 as [H1 []]. repeat split.
      - unfold Relation. intros. apply AxiomII in H5 as [].
        destruct H6 as [x0 [y []]]. exists x0,y. auto.
      - intros. apply AxiomII' in H5 as [], H6 as [].
        destruct H7 as [H7 []], H8 as [H8 []]. subst; auto.
      - apply AxiomI; split; intros.
        + apply AxiomII in H5 as [H5 [y]].
          apply AxiomII' in H6 as [H6 [H7 []]]; auto.
        + assert ((x[z] - a) ∈ ℝ).
          { apply Plus_close; auto. apply H4.
            apply (@ Property_ran z), Property_Value; auto. rewrite H3; auto.
            apply Plus_neg1a; auto. }
          apply AxiomII; split; eauto. exists (x[z] - a).
          apply AxiomII'; repeat split; auto; apply MKT49a; eauto.
      - unfold Included; intros. apply AxiomII in H5 as [H5 [x0]].
        apply AxiomII' in H6 as [H6 [H7 []]]; auto. }
    split; auto.
    intros. pose proof H4. destruct H5. apply H2 in H4. destruct H4 as [N []]. 
    exists N. split; auto. intros. apply H7 in H9; auto.
    destruct H1 as [H1 []]; destruct H3 as [H3 []].
    assert ((x[n] - a) ∈ ℝ).
    { apply Plus_close; auto. apply H11.
      apply (@ Property_ran n),Property_Value; auto. rewrite H10; auto.
      apply Plus_neg1a; auto. }
    assert (x[n] - a = \{\ λ u v, u ∈ ℕ /\ v ∈ ℝ /\ v = x[u] - a \}\ [n]).
    { apply Property_Fun; auto. apply AxiomII'; repeat split; auto.
      apply MKT49a; eauto. }
    assert (\{\ λ u v, u ∈ ℕ /\ v ∈ ℝ /\ v = x[u] - a \}\ [n] ∈ ℝ).
    { apply H13. apply (@ Property_ran n), Property_Value; auto.
      rewrite H12; auto. }
    rewrite Minus_P2; auto. rewrite <-H15; auto.
  - unfold Infinitesimal in H1; unfold Limit_Seq in *; split; auto.
    destruct H1. destruct H1 as [H1 []]. intros. apply H2 in H5.
    destruct H5 as [N []]. exists N; split; auto. intros.
    assert ((x[n] - a) ∈ ℝ).
    { apply Plus_close; auto. destruct H0 as [H0 []]. apply H10.
      apply (@ Property_ran n), Property_Value; auto.
      rewrite H9; auto. apply Plus_neg1a; auto. }
    apply H6 in H8; auto. rewrite Minus_P2 in H8.
    assert (x[n] - a = \{\ λ u v, u ∈ ℕ /\ v ∈ ℝ /\ v = x[u] - a \}\ [n]).
    { apply Property_Fun; auto. apply AxiomII'; repeat split; auto.
      apply MKT49a; eauto. }
    rewrite <-H10 in H8; auto. apply H4. apply (@ Property_ran n),
    Property_Value; auto. rewrite H3; auto.
Qed.

(* 定义3：无穷大数列 *)
Definition Infiniteseries x := IsSeq x /\ (∀ M, M ∈ ℝ /\ 0 < M
  -> ∃ N, N ∈ ℕ /\ ∀ n, n ∈ ℕ -> N < n -> M < Abs [x[n]]).

(* 定义4：正无穷大数列 *)
Definition PosInfiniteseries x := IsSeq x /\ (∀ M, M ∈ ℝ /\ 0 < M
  -> ∃ N, N ∈ ℕ /\ ∀ n, n ∈ ℕ -> N < n -> M < x[n]).

(* 定义5：负无穷大数列 *)
Definition NegInfiniteseries x := IsSeq x /\ (∀ M, M ∈ ℝ /\ 0 < M
  -> ∃ N, N ∈ ℕ /\ ∀ n, n ∈ ℕ -> N < n -> x[n] < -M).
  
(* 2.2 收敛数列性质 *)

Corollary Minus_P3 : ∀ x y, x ∈ ℝ -> y ∈ ℝ -> - (x + y) = (- x) + (- y).
Proof.
  intros. assert ((- (1)) ∈ ℝ). 
  { apply Plus_neg1a; auto. apply one_in_R_Co; auto. }
  assert ((- (1)) · x ∈ ℝ).
  { rewrite <-PlusMult_Co3; auto. apply Plus_neg1a; auto. }
  assert (y · (-(1)) ∈ ℝ).
  { rewrite Mult_P4, <-PlusMult_Co3; auto. apply Plus_neg1a; auto. } 
  rewrite PlusMult_Co3, Mult_P4; auto with real.
  rewrite Mult_P5, Mult_P4, Plus_P4, Mult_P4; auto. symmetry.
  rewrite PlusMult_Co3, Plus_P4, PlusMult_Co3; auto with real.
Qed.

Corollary Minus_P4 : ∀ x, x ∈ ℝ -> - - x = x.
Proof.
  intros. rewrite PlusMult_Co3; auto with real.
  apply PlusMult_Co4; auto.
Qed.

Corollary RMult_eq : ∀ x y z, x ∈ ℝ -> y ∈ ℝ -> z ∈ ℝ -> 
  x = y -> x · z = y · z.
Proof.
  intros. rewrite H2; auto.
Qed.

Corollary RMult_eq' : ∀ x y z, x ∈ ℝ -> y ∈ ℝ -> z ∈ (ℝ ~ [0]) ->
  x · z = y · z -> x = y.
Proof.
  intros. New H1; apply MKT4' in H1 as [].
  assert (z⁻ ∈ (ℝ ~ [0])). { apply Mult_inv1; auto. }
  apply MKT4' in H5 as [].
  apply RMult_eq with (z:= z⁻) in H2; auto with real.
  do 2 rewrite <-Mult_P3 in H2; auto.
  rewrite Divide_P1 in H2; auto. do 2 rewrite Mult_P1 in H2; auto.
Qed. 

(* 定理2.2: 唯一性 *)
Theorem Theorem2_2 : ∀ x a b, IsSeq x -> a ∈ ℝ -> b ∈ ℝ
  -> Limit_Seq x a -> Limit_Seq x b -> a = b.
Proof.
  intros. apply NNPP; intro. apply Limit_Equal in H2 as Ha; auto. 
  assert (((Abs[b-a])/ (1 + 1)) ∈ ℝ  /\ 0 < ((Abs[b-a])/ (1 + 1))).
  { assert (0 < (1 + 1)) as Hb.
    { apply (Order_Co2 _ 1); auto with real.
      left; split; pose proof OrderPM_Co9; auto.
      apply (OrderPM_Co1 _ _ 1) in H5; auto with real.
      rewrite Plus_P4, Plus_P1 in H5; auto with real. destruct H5; auto. }
    assert ((1 + 1) ⁻ ∈ (ℝ ~ [0])) as Hc.
    { apply Mult_inv1. apply MKT4'; split; auto with real.
      apply AxiomII; split; eauto with real.
      intro. apply MKT41 in H5; eauto with real.
      rewrite H5 in Hb. destruct Hb. contradiction. }
    split.
    - apply Mult_close; auto with real. apply MKT4' in Hc; tauto.
    - assert (a ≤ b \/ b ≤ a). { destruct (Leq_P4 a b); auto. }
      destruct H5 as [|].
      + apply Plus_Leq with (z:=(-a)) in H5 as H6; auto with real. 
        rewrite Minus_P1 in H6; auto.
        assert (｜(b - a)｜ = (b - a)). { apply me_zero_Abs; auto with real. }
        rewrite H7. apply OrderPM_Co5; auto with real. apply MKT4' in Hc; tauto.
        left; split.
        * assert (a < b). { split; auto. }
          apply (OrderPM_Co1 _ _ (-a)) in H8; auto with real.
          rewrite Minus_P1 in H8; auto.
        * apply OrderPM_Co10; auto with real.
      + apply Plus_Leq with (z:=(-a)) in H5 as H6; auto with real.
        rewrite Minus_P1 in H6; auto; New H6. 
        apply le_zero_Abs in H7; auto with real.
        assert (｜(b - a)｜ = (- (b - a))). 
        { apply le_zero_Abs; auto with real. }
        assert ((- (b - a)) = (- b + a)).
        { rewrite Minus_P3; auto with real. rewrite Minus_P4; auto. }
        assert ((- b) + a = a + (- b)). { rewrite Plus_P4; auto with real. }
        rewrite H10 in H9. rewrite H9 in H8. rewrite H8.
        apply MKT4' in Hc as []. apply OrderPM_Co5; auto with real.
        left; split; New H5.
        * apply (Plus_Leq _ _ (-b)) in H13; auto with real.
          rewrite Minus_P1 in H13; auto.
          assert (b < a). { split; auto. }
          apply (OrderPM_Co1 _ _ (-b)) in H14; auto with real.
          rewrite Minus_P1 in H14; auto.
        * apply OrderPM_Co10; auto with real. } 
  destruct Ha as []. pose proof H5; destruct H5 as [].
  pose proof H8 as Hz; apply H7 in H8.
  assert (\{ λ u, u ∈ ℕ /\ x[u] ∈ U(b; (｜(b - a)｜ / (1 + 1))) \} ⊂ 
    \{ λ u, u ∈ ℕ /\ x[u] ∉ U(a; (｜(b - a)｜ / (1 + 1)))\} ).
  { unfold Included; intros. apply AxiomII in H10 as [_[]]. 
    apply AxiomII; repeat split; eauto.
    intro. apply AxiomII in H11 as [H11 []];
    apply AxiomII in H12 as [_[_]]. destruct H9, H14, H12.
    apply Abs_P4 in H14 as [], H12 as []; auto with real.
    assert (0 ≤ (b - a) \/ (b - a) ≤ 0).
    { destruct (Leq_P4 (b-a) 0) as [|]; auto with real. }
    assert (｜(b - a)｜ = b - a \/ ｜(b - a)｜ = a - b).
    { destruct H20 as [|].
      - left. apply me_zero_Abs; auto with real.
      - right. assert (｜(b - a)｜ = (- (b - a))). 
        { apply le_zero_Abs; auto with real. }
        assert ((- (b - a)) = (- b + a)).
        { rewrite Minus_P3, Minus_P4; auto with real. }
        rewrite H21; rewrite H22; apply Plus_P4; auto with real. }
    assert (0 < (1 + 1)) as Ha.
    { apply (Order_Co2 _ 1); auto with real.
      left; split; New OrderPM_Co9; auto.
      apply (OrderPM_Co1 _ _ 1) in H22; auto with real.
      rewrite Plus_P4, Plus_P1 in H22; auto with real. destruct H22; auto. } 
    assert ((1 + 1) ⁻ ∈ (ℝ ~ [0])) as Hb.
    { apply Mult_inv1. apply MKT4'; split; auto with real.
      apply AxiomII; split; eauto with real.
      intro. apply MKT41 in H22; eauto with real.
      rewrite H22 in Ha. destruct Ha; contradiction. }
    pose proof Hb as Hc; apply MKT4' in Hc as [Hd He].
    assert (a = ((1 + 1) · a) / (1 + 1)) as Hf.
    { assert (a · (1 + 1) = (1 + 1) · a).
      { rewrite Mult_P4; auto with real. }
      apply RMult_eq with (z:=(1 + 1)⁻) in H22; auto with real.
      rewrite <-Mult_P3, Divide_P1, Mult_P1 in H22; auto with real.
      apply MKT4'; split; auto with real.
      apply AxiomII; split; eauto with real. 
      intro. apply MKT41 in H23; eauto with real.
      rewrite H23 in Ha; destruct Ha; eauto. }
    assert (b = ((1 + 1) · b) / (1 + 1)) as Hg.
    { assert (b · (1 + 1) = (1 + 1) · b).
      { apply Mult_P4; auto with real. }
      apply RMult_eq with (z:=(1 + 1)⁻) in H22; auto with real.
      rewrite <-Mult_P3, Divide_P1, Mult_P1 in H22; auto with real.
      apply MKT4'; split; auto with real.
      apply AxiomII; split; eauto with real.
      intro. apply MKT41 in H23; eauto with real.
      rewrite H23 in Ha; destruct Ha; contradiction. }
    assert ((1 + 1) · a = a + a) as Hh.
    { rewrite Mult_P5, Mult_P4, Mult_P1; auto with real. }
    assert ((1 + 1) · b = b + b) as Hi.
    { rewrite Mult_P5, Mult_P4, Mult_P1; auto with real. }
    destruct H21 as [|].
    - rewrite H21 in *.
      (* b - ε *)
      apply (Plus_Leq _ _ b) in H14; auto with real;
      rewrite <-Plus_P3, (Plus_P4 (- b)), Minus_P1, Plus_P1 in H14; 
      auto with real.
      pattern b at 2 in H14; rewrite Hg in H14.
      rewrite PlusMult_Co3, Mult_P3, <-Mult_P5 in H14; auto with real.
      rewrite <-PlusMult_Co3, Minus_P3, Minus_P4 in H14; auto with real.
      rewrite Hi, Plus_P4, <-Plus_P3, Plus_P4 in H14; auto with real.
      rewrite Plus_P3, Plus_neg2, (Plus_P4 0), Plus_P1 in H14; auto with real.
      (* a + ε *) 
      apply (Plus_Leq _ _ a) in H19; auto with real; 
      rewrite <-Plus_P3, (Plus_P4 (-a)), Minus_P1, Plus_P1 in H19;
      auto with real.
      pattern a at 2 in H19; rewrite Hf in H19.
      rewrite <-Mult_P5, Hh in H19; auto with real.
      rewrite Plus_P4, (Plus_P4 b), Plus_P3 in H19; auto with real.
      rewrite <-(Plus_P3 a), Plus_neg2, Plus_P1 in H19; auto with real.
      (* elim *)
      assert (x [z] = (a + b) · ((1 + 1) ⁻)).
      { apply Leq_P2; auto with real. }
      elim H17. rewrite H22. pattern a at 2; rewrite Hf.
      rewrite PlusMult_Co3, Mult_P3, <-Mult_P5; auto with real.
      rewrite <-PlusMult_Co3, Hh, Minus_P3; auto with real.
      rewrite (Plus_P4 a), <-Plus_P3, (Plus_P3 a); auto with real.
      rewrite Plus_neg2, (Plus_P4 0), Plus_P1; auto with real.
      apply me_zero_Abs; auto.
    - rewrite H21 in *.
      (* a - ε *)
      apply (Plus_Leq _ _ a) in H12; auto with real;
      rewrite <-Plus_P3, (Plus_P4 ((- a))), Plus_neg2, (Plus_P1) in H12; 
      auto with real.
      pattern a at 2 in H12; rewrite Hf in H12.
      rewrite PlusMult_Co3, Mult_P3, <-PlusMult_Co3 in H12; auto with real.
      rewrite <-Mult_P5, Hh in H12; auto with real.
      rewrite Minus_P3, Minus_P4, (Plus_P4 (-a)) in H12; auto with real.
      rewrite <-Plus_P3,(Plus_P3 (-a)),(Plus_P4 (-a)) in H12; auto with real. 
      rewrite Plus_neg2, (Plus_P4 0), Plus_P1 in H12; auto with real.
      (* b + ε *)
      apply (Plus_Leq _ _ b) in H18; auto with real;
      rewrite <-Plus_P3, (Plus_P4 (- b)), Plus_neg2, Plus_P1 in H18;
      auto with real.
      pattern b at 2 in H18; rewrite Hg in H18.
      rewrite <-Mult_P5, Hi in H18; auto with real.
      rewrite <-Plus_P3, (Plus_P4 (- b)), <-Plus_P3 in H18; auto with real.
      rewrite Plus_neg2, Plus_P1, Plus_P4 in H18; auto with real.
      (* elim *)
      assert (x[z] = (b + a) · ((1 + 1)⁻)).
      { apply Leq_P2; auto with real. }
      elim H16. rewrite H22. pattern b at 2; rewrite Hg.
      rewrite PlusMult_Co3, Mult_P3, <-Mult_P5; auto with real.
      rewrite Hi, <-PlusMult_Co3, Minus_P3; auto with real.
      rewrite (Plus_P4 b), <-Plus_P3, (Plus_P3 b); auto with real.
      rewrite Plus_neg2, (Plus_P4 0), Plus_P1; auto with real.
      apply me_zero_Abs; auto. }
  apply finsub in H10; auto. unfold Limit_Seq in H3; destruct H3 as [].
  apply H11 in Hz as H12. destruct H12 as [N2 []]. apply finite_maxN in H10.
  destruct H10 as [N1]; unfold maxR in H10; destruct H10 as [H10 []].
  destruct (Leq_P4 N1 N2) as [Ha | Ha]; auto with real.
  - assert (N2 < (N2 + 1)).
    { pose proof H12; apply N_Subset_R in H16; apply Leq_P1 in H16.
      destruct OrderPM_Co9. apply (OrderPM_Co3 _ _ 0 1) in H16; auto with real.
      rewrite Plus_P1 in H16; auto with real. split; auto.
      intro. assert (N2 - N2 = N2 + 1 - N2). { rewrite <-H19; auto. }
      rewrite Plus_neg2, (Plus_P4 N2), <-Plus_P3, Plus_neg2, Plus_P1 in H20;
      auto with real. }
      apply H13 in H16; auto with real.
    assert (N2 + 1 ∈ \{ λ u, u ∈ ℕ /\ x[u] ∈ U(b; (｜(b - a)｜/(1 + 1))) \}).
    { destruct H6 as [H6 []]; destruct H16.
      assert (x[N2 + 1] ∈ ℝ).
      { apply H18. apply (@ Property_ran (N2 + 1)), Property_Value; auto.
        rewrite H17; auto with real. }
      apply AxiomII; repeat split; eauto with real.
      apply AxiomII; repeat split; eauto. }
    apply H15 in H17. apply AxiomII in H14 as [_[]].
    assert (N1 < N2 + 1). { apply Nat_P4b; auto. }
    destruct H19. elim H20. apply Leq_P2; auto with real.
  - apply AxiomII in H14 as [_[]].
    assert (N2 < N1 + 1). { apply Nat_P4b; auto. }
    pose proof H16. apply H13 in H17; auto with real.
    assert (N1 + 1 ∈ \{ λ u, u ∈ ℕ /\ x[u] ∈ U(b; (｜(b - a)｜/(1 + 1))) \}).
    { destruct H17; auto. destruct H6 as [H6 []].
      assert (x[N1 + 1] ∈ ℝ).
      { apply H21, (@ Property_ran (N1 + 1)), Property_Value; auto. 
        rewrite H20; auto with real. }
      apply AxiomII; repeat split; eauto with real.
      apply AxiomII; repeat split; eauto with real. }
    assert (N1 < N1 + 1).
    { apply Nat_P4b; auto; apply Leq_P1; auto with real. }
    apply H15 in H19. destruct H20. elim H21. apply Leq_P2; auto with real.
  - assert (N2 < N2 + 1).
    { apply Nat_P4b; auto; apply Leq_P1; auto with real. }
    apply H13 in H14; auto with real. apply NEexE; exists (N2 + 1).
    destruct H6 as [H6 []]; destruct H14.
    assert (x[N2 + 1] ∈ ℝ).
    { apply H16. apply (@ Property_ran (N2 + 1)), Property_Value; auto.
      rewrite H15; auto with real. }
    apply AxiomII; repeat split; eauto with real.
    apply AxiomII; repeat split; eauto with real.
  - unfold Included; intros. apply AxiomII in H14; tauto.
Qed.

Definition lim x := ∩(\{ λ a, a ∈ ℝ /\ Limit_Seq x a \}).

Theorem Lim_getValue : ∀ x a, IsSeq x -> a ∈ ℝ -> Limit_Seq x a -> lim x = a.
Proof.
  intros. apply AxiomI; split; intros.
  - apply AxiomII in H2 as []. apply H3. apply AxiomII; split; eauto.
  - apply AxiomII; split; eauto. intros. apply AxiomII in H3 as [H3 []].
    assert (a = y). { apply Theorem2_2 with x; auto. }
    rewrite <-H6; auto.
Qed.

(* Definition Convergence x := IsSeq x -> ∃ a, a ∈ ℝ /\ Limit_Seq x a. *)

Corollary RMult_eq_N1 : ∀ x, x ∈ ℝ -> x / (-(1)) = (-(1)) · x.
Proof.
  intros. pose proof OrderPM_Co9 as H0; destruct H0.
  assert ((-(1)) ∈ (ℝ ~ [0])).
  { apply MKT4'; split; auto with real.
    apply AxiomII; split; eauto with real. intro. apply MKT41 in H2;
    eauto with real. apply (RMult_eq _ _ (-(1))) in H2; auto with real.
    rewrite <-PlusMult_Co3, Minus_P4, Mult_P4, PlusMult_Co1 in H2;
    auto with real. }
  assert ((-(1))⁻ ∈ (ℝ ~ [0])). { auto with real. }
  apply MKT4' in H3 as []. apply (RMult_eq' _ _ (-(1))); auto with real. 
  rewrite Mult_P4, (Mult_P4 x), Mult_P3, Divide_P1, Mult_P4, Mult_P1,
  Mult_P4, <-PlusMult_Co3, <-PlusMult_Co3; auto with real.
  symmetry; apply Minus_P4; auto.
Qed.

(* Ropp_lt_gt_contravar *)
Corollary OrderPM_Co12a : ∀ x y, x ∈ ℝ -> y ∈ ℝ -> x < y <-> - y < - x.
Proof.
  assert ((-(1)) < 0).
  { pose proof OrderPM_Co9. apply OrderPM_Co2a in H; auto with real. }
  split; intros.
  - apply (OrderPM_Co8a _ _ (-(1))) in H2; auto with real.
    rewrite Mult_P4, (Mult_P4 x), <-PlusMult_Co3, <-PlusMult_Co3 in H2;
    auto with real.
  - apply (OrderPM_Co8a _ _ (-(1))) in H2; auto with real.
    rewrite Mult_P4, (Mult_P4 (-(y))), PlusMult_Co4, PlusMult_Co4 in H2;
    auto with real.
Qed.

Corollary OrderPM_Co12b : ∀ x y, x ∈ ℝ -> y ∈ ℝ -> x ≤ y <-> - y ≤ - x.
Proof.
  assert ((-(1)) < 0) as [Ha Hb].
  { pose proof OrderPM_Co9. apply OrderPM_Co2a in H; auto with real. }
  split; intros.
  - apply (OrderPM_Co8b _ _ (-(1))) in H1; auto with real.
    rewrite Mult_P4, (Mult_P4 x), <-PlusMult_Co3, <-PlusMult_Co3 in H1;
    auto with real.
  - apply (OrderPM_Co8b _ _ (-(1))) in H1; auto with real.
    rewrite Mult_P4, (Mult_P4 (- y)), PlusMult_Co4, PlusMult_Co4 in H1;
    auto with real.
Qed.

(* 定理2.3: 有界性 *)
Theorem Theorem2_3' : ∀ x, IsSeq x -> Convergence x 
  -> (∃ M, M ∈ ℝ /\ (∀ n, n ∈ ℕ -> ｜(x[n])｜ ≤ M)).
Proof.
  intros. destruct H0 as [a [H0]]. destruct H1 as [].
  destruct H1 as [H1 []]; New OrderPM_Co9.
  assert (1 ∈ ℝ /\ 0 < 1). { split; auto with real. }
  apply H2 in H6 as H7; destruct H7 as [N []]. destruct H5.
  set (F := \{ λ N1, N1 ∈ ℕ 
    /\ (∃ M, M ∈ ℝ /\ ∀ n, n ∈ ℕ -> n ≤ N1 -> ｜(x[n])｜ ≤ M) \}).
  assert (F = ℕ).
  { apply MathInd_Ma. unfold Included; intros.
    - apply AxiomII in H10 as [_[]]; auto.
    - assert (｜(x [1])｜ ∈ ℝ) as Ha.
      { apply Abs_in_R, H4, (@ Property_ran 1), Property_Value; auto.
        rewrite H3; auto with real. }
      apply AxiomII; repeat split; eauto with real.
      exists (｜(x [1])｜).
      { split; auto; intros.
        assert (n = 1).
        { pose proof one_is_min_in_N as H12; destruct H12 as [H12 []].
          apply H14 in H10 as H15. apply Leq_P2; auto. }
        rewrite H12. apply Leq_P1; auto. }
    - intros. apply AxiomII in H10 as [_[]]; destruct H11 as [M []].
      apply AxiomII; repeat split; eauto with real.
      assert (｜(x [x0 + 1])｜ ∈ ℝ).
      { apply Abs_in_R, H4, (@ Property_ran (x0 + 1)), Property_Value; auto.
        rewrite H3; auto with real. }
      destruct (Leq_P4 ｜(x[x0 + 1])｜ M) as [H14 | H14]; auto.
      + exists M; split; auto. intros. destruct (classic (n = x0 + 1)).
        * rewrite H17; auto.
        * assert (n < x0 + 1). { split; auto. }
          apply Nat_P4 in H18; auto with real.
          apply (Plus_Leq _ _ (-(1))) in H18; auto with real.
          do 2 rewrite <-Plus_P3 in H18; auto with real.
          do 2 rewrite Plus_neg2 in H18; auto with real.
          do 2 rewrite Plus_P1 in H18; auto with real.
      + exists ｜(x [x0 + 1])｜; split; auto. intros.
        assert (｜(x[n])｜ ∈ ℝ).
        { apply Abs_in_R, H4, (@ Property_ran n), Property_Value; auto.
          rewrite H3; auto. }
        destruct (classic (n = x0 + 1)).
        * rewrite H18; apply (Leq_P1); auto.
        * assert (n < x0 + 1). { split; auto. }
          assert (｜(x [n])｜ ≤ M).
          { apply Nat_P4 in H19; auto with real.
            apply (Plus_Leq _ _ (-(1))) in H19; auto with real.
            do 2 rewrite <-Plus_P3 in H19; auto with real.
            do 2 rewrite Plus_neg2 in H19; auto with real.
            do 2 rewrite Plus_P1 in H19; auto with real. }
          apply (Leq_P3 _ M _); auto. }
  rewrite <-H10 in H7; apply AxiomII in H7 as [_[]].
  assert ((-(1)) ∈ (ℝ ~ [0])) as Ha.
  { apply MKT4'; split; auto with real.
    apply AxiomII; split; eauto with real. intro. apply MKT41 in H12;
    eauto with real. apply (RMult_eq _ _ (-(1))) in H12; auto with real.
    rewrite <-PlusMult_Co3, Minus_P4, Mult_P4, PlusMult_Co1 in H12;
    auto with real. }
  assert ((-(1))⁻ ∈ (ℝ ~ [0])) as Hb. { auto with real. }
  apply MKT4' in Hb as [Hb Hc].
  destruct H11 as [M [H11]]. destruct (Leq_P4 a 0); auto with real.
  - assert (∀ n, n ∈ ℕ -> N < n -> ｜(x [n])｜ < 1 - a).
    { intros. assert (x[n] ∈ ℝ).
      { apply H4, (@ Property_ran n), Property_Value; auto; rewrite H3; auto. }
      assert (0 ≤ (- a)).
      { apply (Plus_Leq _ _ (- a)) in H13 as H17; auto with real.
        rewrite Plus_neg2, Plus_P4, Plus_P1 in H17; auto with real. }
      assert (0 ≤ 1 - a).
      { assert (0 + 0 ≤ 1 + (- a)).
        { apply OrderPM_Co3; auto with real. }
        rewrite Plus_P1 in H18; auto with real. }
      apply H8 in H15; auto. destruct H15. 
      apply Abs_P4 in H15 as [];
      auto with real. split. apply Abs_P4; auto with real.
      apply (Plus_Leq _ _ a) in H15; auto with real.
      rewrite <-Plus_P3, (Plus_P4 (- a)), Plus_neg2, Plus_P1 in H15; 
      auto with real.
      apply (Plus_Leq _ _ a) in H20; auto with real.
      rewrite <-Plus_P3, (Plus_P4 (- a)), Plus_neg2, Plus_P1 in H20;
      auto with real.
      split. rewrite Minus_P3, Minus_P4; auto with real.
      assert (1 + a ≤ 1 - a).
      { apply OrderPM_Co3; auto with real. apply Leq_P1; auto with real.
        apply (Leq_P3 _ 0 _); auto with real. }
      apply (Leq_P3 _ (1 + a) _); auto with real.
      intro. elim H19.
      destruct (Leq_P4 (x[n]) 0) as [H22 | H22]; auto with real.
      -- assert (｜(x [n])｜ = - x[n]). { apply le_zero_Abs; auto. }
         rewrite H23, PlusMult_Co3, Mult_P4 in H21; auto with real.
         apply (RMult_eq _ _ ((-(1))⁻)) in H21; auto with real.
         rewrite <-Mult_P3, Divide_P1, Mult_P1 in H21; auto with real.
         rewrite H21. assert ((1 - a) / - (1) = (- (1)) + a).
         { assert ((1 - a) / - (1) = (-(1)) · (1 - a)).
           { apply RMult_eq_N1; auto with real. }
           rewrite H24, <-PlusMult_Co3, Minus_P3, Minus_P4; auto with real. }
         rewrite H24. rewrite <-Plus_P3, Plus_neg2, Plus_P1; auto with real.
         assert (｜1｜ = ｜(-(1))｜). { apply Abs_P2; auto with real. }
         rewrite <-H25; apply me_zero_Abs; auto with real.
      -- (* ▲ *)
         assert (｜(x[n])｜ = x[n]). { apply me_zero_Abs; auto. }
         rewrite H23 in H21. rewrite H21, <-Plus_P3 in H20; auto with real.
         assert (- a - a = (- a) · (1 + 1)).
         { rewrite Mult_P4, Mult_P5, Mult_P4, Mult_P1, PlusMult_Co3;
           auto with real. }
         (* ****** rewrite H24 in H20. ****** *)
         assert (1 + ((- a)+ (- a)) ≤ 1); auto. rewrite H24 in H25.
         assert (0 ≤ (- a)· (1 + 1)).
         { apply (OrderPM_Co7b _ _ (1 + 1)) in H17; auto with real.
           rewrite Mult_P4, PlusMult_Co1 in H17; auto with real.
           assert (0 + 0 ≤ 1 + 1). { apply OrderPM_Co3; auto with real. }
           rewrite Plus_P1 in H26; auto with real. }
         assert (1 ≤ 1 + ((- a)· (1 + 1))).
         { assert (1 + 0 ≤ 1 + ((- a)· (1 + 1))).
           { apply OrderPM_Co3; auto with real. apply Leq_P1; auto with real. }
           rewrite Plus_P1 in H27; auto with real. }
         assert (1 = 1 + (- a) · (1 + 1)). { apply Leq_P2; auto with real. }
         rewrite H28, H21. assert ((1 - a) - a = 1 + (- a - a)). (* * *)
         { rewrite <-Plus_P3; auto with real. }
         rewrite H29, H24. apply me_zero_Abs; auto with real.
         assert (0 + 0 ≤ 1 + ((- a)· (1 + 1))).
         { apply OrderPM_Co3; auto with real. }
         rewrite Plus_P1 in H30; auto with real. }
    destruct (Leq_P4 (1 - a) M) as [H15 | H15]; auto with real.
    + exists M; split; auto. intros.
      destruct (Order_Co1 n N) as [H17 | [|]]; auto with real.
      * destruct H17. apply H12 in H17; auto.
      * apply H14 in H17; auto. destruct H17.
        apply (Leq_P3 _ (1 - a) _); auto with real.
        apply Abs_in_R, H4, (@ Property_ran n), Property_Value; auto.
        rewrite H3; auto.
      * apply H12; auto. rewrite H17. apply Leq_P1; auto with real.
    + exists (1 - a); split; auto with real. intros.
      destruct (Order_Co1 n N) as [H17 | [|]]; auto with real.
      * destruct H17. apply H12 in H17; auto.
        apply (Leq_P3 _ M _); auto with real.
        apply Abs_in_R, H4, (@ Property_ran n), Property_Value; auto.
        rewrite H3; auto.
      * apply H14 in H17; destruct H17; auto.
      * assert (｜(x[N])｜ ≤ M).
        { rewrite <-H17. apply H12; auto. rewrite H17.
          apply Leq_P1; auto with real. }
        rewrite H17. apply (Leq_P3 _ M _); auto with real.
        apply Abs_in_R, H4, (@ Property_ran N), Property_Value; auto.
        rewrite H3; auto.
  - assert (∀ n, n ∈ ℕ -> N < n -> ｜(x [n])｜ < 1 + a).
    { intros. assert (x[n] ∈ ℝ).
      { apply H4, (@ Property_ran n), Property_Value; auto; rewrite H3; auto. }
      assert (- a ≤ 0).
      { apply (Plus_Leq _ _ (- a)) in H13; auto with real.
        rewrite Plus_neg2, (Plus_P4 0), Plus_P1 in H13; auto with real. }
      assert (0 ≤ 1 + a).
      { assert (0 + 0 ≤ 1 + a).
        { apply OrderPM_Co3; auto with real. }
        rewrite Plus_P1 in H18; auto with real. }
      apply H8 in H15; auto. destruct H15; apply Abs_P4 in H15 as [];
      auto with real. split. apply Abs_P4; auto with real.
      apply (Plus_Leq _ _ a) in H20; auto with real.
      rewrite <-Plus_P3, (Plus_P4 (- a)), Plus_neg2, Plus_P1 in H20;
      auto with real.
      apply (Plus_Leq _ _ a) in H15; auto with real.
      rewrite <-Plus_P3, (Plus_P4 (- a)), Plus_neg2, Plus_P1 in H15;
      auto with real. split; auto.
      assert ((-(1)) - a ≤ (-(1)) + a).
      { apply OrderPM_Co3; auto with real. apply Leq_P1; auto with real.
        apply (Leq_P3 _ 0 _); auto with real. }
      rewrite Minus_P3; auto with real. apply (Leq_P3 _ ((-(1)) + a) _);
      auto with real. intro. elim H19.
      destruct (Leq_P4 (x [n]) 0) as [H22 | H22]; auto with real.
      (* ▲ *)
      -- assert (｜(x[n])｜ = - x[n]). { apply le_zero_Abs; auto. }
         assert (-(1) < 0) as [Hz Hy].
         { pose proof OrderPM_Co9. apply OrderPM_Co2a in H24; auto with real. }
         rewrite H23, PlusMult_Co3, Mult_P4 in H21; auto with real.
         apply (RMult_eq _ _ ((-(1))⁻)) in H21; auto with real.
         rewrite <-Mult_P3, Divide_P1, Mult_P1 in H21; auto with real.
         rewrite RMult_eq_N1 in H21; auto with real.
         assert (a + a = a · (1 + 1)).
         { rewrite Mult_P4, Mult_P5, Mult_P4, Mult_P1; auto with real. }
         assert (0 ≤ a · (1 + 1)).
         { apply (OrderPM_Co7b _ _ (1 + 1)) in H13; auto with real.
           rewrite Mult_P4, PlusMult_Co1 in H13; auto with real.
           assert (0 + 0 ≤ 1 + 1). { apply OrderPM_Co3; auto with real. }
           rewrite Plus_P1 in H25; auto with real. }
         assert (1 ≤ 1 + a · (1 + 1)).
         { assert (1 + 0 ≤ 1 + a · (1 + 1)).
           { apply OrderPM_Co3; auto with real; apply Leq_P1; auto with real. }
           rewrite Plus_P1 in H26; auto with real. }
         rewrite H21 in H15.
         assert (- (a) = (- (1)) · a). { rewrite PlusMult_Co3; auto. }
         rewrite H27, Mult_P4, (Mult_P4 (-(1))), <-Mult_P5, <-Plus_P3,
         Mult_P4, <-PlusMult_Co3 in H15; auto with real.
         apply (OrderPM_Co8b _ _ (-(1))) in H15; auto with real.
         rewrite Mult_P4, PlusMult_Co4, PlusMult_Co4 in H15; auto with real.
         (* ****** rewrite H24 in H15 ****** *)
         assert (1 + (a + a) ≤ 1); auto. rewrite H24 in H28.
         assert (1 = 1 + a · (1 + 1)). { apply Leq_P2; auto with real. }
         rewrite H29, H21. rewrite H27, Mult_P4, (Mult_P4 (-(1))), <-Mult_P5,
         Mult_P4, <-PlusMult_Co3, <-Plus_P3; auto with real.
         assert (｜(- (1 + (a + a)))｜ = 1 + a · (1 + 1)).
         { assert (0 ≤ (1 + a · (1 + 1))).
           { apply (Leq_P3 _ 1 _); auto with real. }
           assert (｜(1 + a · (1 + 1))｜ = ｜(- (1 + a · (1 + 1)))｜).
           { pose proof (Abs_P2 (1 + a · (1 + 1))) as [Hx _]; auto with real. }
           rewrite H24, <-H31. apply me_zero_Abs; auto with real. } auto.
      -- assert (｜(x[n])｜ = x[n]). { apply me_zero_Abs; auto. }
         rewrite H23 in H21. rewrite H21, <-Plus_P3, Plus_neg2, Plus_P1;
         auto with real. apply me_zero_Abs; auto with real. }
    destruct (Leq_P4 (1 + a) M) as [H15 | H15]; auto with real.
    + exists M; split; auto. intros.
      destruct (Order_Co1 n N) as [H17 | [|]]; auto with real.
      * destruct H17; apply H12 in H17; auto.
      * apply H14 in H17; destruct H17; auto.
        apply (Leq_P3 _ (1 + a) _); auto with real.
        apply Abs_in_R, H4, (@ Property_ran n), Property_Value; auto.
        rewrite H3; auto.
      * apply H12; auto. rewrite H17; apply Leq_P1; auto with real.
    + exists (1 + a); split; auto with real. intros.
      destruct (Order_Co1 n N) as [H17 | [|]]; auto with real.
      * destruct H17; apply H12 in H17; auto.
        apply (Leq_P3 _ M _); auto with real.
        apply Abs_in_R, H4, (@ Property_ran n), Property_Value; auto.
        rewrite H3; auto.
      * apply H14 in H17; destruct H17; auto.
      * assert (｜(x[N])｜ ≤ M).
        { rewrite <-H17. apply H12; auto. rewrite H17; apply Leq_P1;
          auto with real. }
        apply (Leq_P3 _ M _); auto with real.
        apply Abs_in_R, H4, (@ Property_ran n), Property_Value; auto.
        rewrite H3; auto. rewrite H17; auto.
Qed.

Theorem Theorem2_3 : ∀ x, IsSeq x -> Convergence x
  -> (∃ M, M ∈ ℝ /\ 0 < M /\ (∀ n, n ∈ ℕ -> ｜(x[n])｜ ≤ M)).
Proof.
  intros. apply Theorem2_3' in H0; auto.
  destruct H0 as [M []], H as [H []].
  assert (0 ≤ M).
  { pose proof one_in_N; apply (H1 1) in H4 as H5.
    apply (Leq_P3 _ ｜(x [1])｜ _); auto with real. apply Abs_in_R,
    H3, (@ Property_ran 1), Property_Value; auto; rewrite H2; auto.
    apply Abs_P1. apply H3, (@ Property_ran 1), Property_Value; auto.
    rewrite H2; auto. }
  destruct (classic (M = 0)).
  - exists (M + 1); split; auto with real; pose proof OrderPM_Co9.
    split. rewrite H5, Plus_P4, Plus_P1; auto with real.
    intros; apply (Leq_P3 _ M _); auto with real. apply Abs_in_R, H3,
    (@ Property_ran n), Property_Value; auto; rewrite H2; auto.
    destruct H6; rewrite H5, Plus_P4, Plus_P1; auto with real.
  - exists M; repeat split; auto.
Qed.
    
Corollary RPlus_eq : ∀ x y z, x ∈ ℝ -> y ∈ ℝ -> z ∈ ℝ -> x = y -> x + z = y + z.
Proof.
  intros. rewrite H2; auto.
Qed.

Corollary RPlus_eq' : ∀ x y z, x ∈ ℝ -> y ∈ ℝ -> z ∈ ℝ -> x + z = y + z -> x = y.
Proof.
  intros. apply (RPlus_eq _ _ (- z)) in H2; auto with real.
  rewrite <-Plus_P3, <-Plus_P3, Plus_neg2, Plus_P1, Plus_P1 in H2;
  auto with real.
Qed.

(* 定理2.4 保号性*)
Theorem Theorem2_4_1 : ∀ x a, IsSeq x -> a ∈ ℝ -> Limit_Seq x a -> 0 < a
  -> (∀ a', a' ∈ ℝ /\ a' ∈ ］0,a［ 
    -> (∃ N, N ∈ ℕ /\ (∀ n, n ∈ ℕ -> N < n -> a' < x[n]))).
Proof.
  intros. destruct H1 as [Ha Hb], H3 as [Hc Hd], Ha as [He [Hf Hg]].
  apply AxiomII in Hd as [_[_[]]].
  assert (a - a' ∈ ℝ /\ 0 < a - a').
  { split; auto with real. destruct H3; split.
    apply (Plus_Leq _ _ (- a')) in H3; auto with real.
    rewrite Plus_neg2 in H3; auto. intro. elim H4.
    apply (RPlus_eq' _ _ (- a')); auto with real. rewrite Plus_neg2; auto. }
  apply Hb in H4 as [N []]. exists N; split; auto; intros.
  assert (x[n] ∈ ℝ) as Hh.
  { apply Hg, (@ Property_ran n), Property_Value; auto. rewrite Hf; auto. }
  assert (0 ≤ (a - a')) as Hi.
  { destruct H3. apply (Plus_Leq _ _ (- a')) in H3; auto with real.
    rewrite Plus_neg2 in H3; auto. }
  assert (a' - a ≤ 0) as Hj.
  { destruct H3. apply (Plus_Leq _ _ (- a)) in H3; auto with real.
    rewrite Plus_neg2 in H3; auto. }
  apply H5 in H7; auto. destruct H7.
  apply Abs_P4 in H7 as []; auto with real.
  rewrite Minus_P3, Minus_P4 in H7; auto with real.
  apply (Plus_Leq _ _ a) in H7; auto with real.
  rewrite Plus_P4,Plus_P3,Plus_neg2,(Plus_P4 0),Plus_P1 in H7; auto with real.
  rewrite <-Plus_P3, (Plus_P4 (- a)), Plus_neg2, Plus_P1 in H7; auto with real.
  split; auto. intro. elim H8. rewrite <-H10. 
  assert (a - a' = - (a' - a)).
  { rewrite Minus_P3, Minus_P4, Plus_P4; auto with real. }
  rewrite H11. apply le_zero_Abs; auto with real.
Qed.

Theorem Theorem2_4_2 : ∀ x a, IsSeq x -> a ∈ ℝ -> Limit_Seq x a -> a < 0
  -> (∀ a', a' ∈ ℝ /\ a' ∈ ］a,0［
    -> (∃ N, N ∈ ℕ /\ (∀ n, n ∈ ℕ -> N < n -> x[n] < a'))).
Proof.
  intros. destruct H1 as [Ha Hb], Ha as [Hc [Hd He]], H3 as [Hf Hg].
  apply AxiomII in Hg as [_[_[]]].
  assert ((a' - a) ∈ ℝ /\ 0 < (a' - a)).
  { split; auto with real. destruct H1. apply (Plus_Leq _ _ (- a)) in H1; 
    auto with real; rewrite Plus_neg2 in H1; auto. split; auto. intro. elim H4.
    apply (RPlus_eq' _ _ (- a)); auto with real; rewrite Plus_neg2; auto. }
  apply Hb in H4. destruct H4 as [N []]. exists N; split; auto. intros.
  assert (x[n] ∈ ℝ).
  { apply He, (@ Property_ran n), Property_Value; auto. rewrite Hd; auto. }
  assert (0 ≤ a' - a).
  { destruct H1. apply (Plus_Leq _ _ (- a)) in H1; auto with real.
    rewrite Plus_neg2 in H1; auto. }
  apply H5 in H7; auto. destruct H7. apply Abs_P4 in H7 as []; auto with real.
  apply (Plus_Leq _ _ a) in H11; auto with real.
  rewrite <-Plus_P3, <-Plus_P3, (Plus_P4 (-(a))) in H11; auto with real.
  rewrite Plus_neg2, Plus_P1, Plus_P1 in H11; auto. split; auto.
  intro. elim H10. rewrite H12. apply me_zero_Abs; auto with real.
Qed.

Corollary Max_nat_3 : ∀ N0 N1 N2, N0 ∈ ℕ -> N1 ∈ ℕ -> N2 ∈ ℕ
  -> (∃ N, N ∈ ℕ /\ N0 < N /\ N1 < N /\ N2 < N).
Proof.
  intros. destruct (Leq_P4 N0 N1) as [Ha | Ha]; auto with real.
  - destruct (Leq_P4 N1 N2) as [Hb | Hb]; auto with real.
    + exists (N2 + 1).
      assert (N0 < N2 + 1) as []. 
      { apply Nat_P4b; auto; apply (Leq_P3 _ N1 _); auto with real. }
      assert (N1 < N2 + 1) as []. { apply Nat_P4b; auto. }
      assert (N2 < N2 + 1) as [].
      { apply Nat_P4b; auto; apply Leq_P1; auto with real. }
      repeat split; auto with real.
    + exists (N1 + 1).
      assert (N0 < N1 + 1) as []. { apply Nat_P4b; auto. }
      assert (N1 < N1 + 1) as []. 
      { apply Nat_P4b; auto; apply Leq_P1; auto with real. }
      assert (N2 < N1 + 1) as []. { apply Nat_P4b; auto. }
      repeat split; auto with real.
  - destruct (Leq_P4 N0 N2) as [Hb | Hb]; auto with real.
    + exists (N2 + 1).
      assert (N0 < N2 + 1) as []. { apply Nat_P4b; auto. }
      assert (N1 < N2 + 1) as [].
      { apply Nat_P4b; auto. apply (Leq_P3 _ N0 _); auto with real. }
      assert (N2 < N2 + 1) as [].
      { apply Nat_P4b; auto; apply Leq_P1; auto with real. }
      repeat split; auto with real.
    + exists (N0 + 1).
      assert (N0 < N0 + 1) as [].
      { apply Nat_P4b; auto; apply Leq_P1; auto with real. }
      assert (N1 < N0 + 1) as []. { apply Nat_P4b; auto. }
      assert (N2 < N0 + 1) as []. { apply Nat_P4b; auto. }
      repeat split; auto with real.
Qed.

Corollary Max_nat_2 : ∀ N0 N1, N0 ∈ ℕ -> N1 ∈ ℕ -> 
  (∃ N, N ∈ ℕ /\ N0 < N /\ N1 < N).
Proof.
  intros. pose proof (Max_nat_3 _ _ _ H H0 H0).
  destruct H1 as [N [H1 [H2 [_]]]]. exists N; split; auto.
Qed.

Corollary Rnot_le_gt : ∀ r1 r2, r1 ∈ ℝ -> r2 ∈ ℝ -> ~ (r1 ≤ r2) <-> (r2 < r1).
Proof.
  split; intros.
  - apply NNPP; intro. destruct (Leq_P4 r1 r2); auto.
    destruct (classic (r1 = r2)).
    + rewrite H4 in H1. elim H1. apply Leq_P1; auto.
    + elim H2; auto. split; auto.
  - intro. destruct H1. elim H3. apply Leq_P2; auto.
Qed.

Corollary Rnot_lt_ge : ∀ r1 r2, r1 ∈ ℝ -> r2 ∈ ℝ -> ~ (r1 < r2) <-> r2 ≤ r1.
Proof.
  split; intros.
  - apply NNPP; intro. destruct (Leq_P4 r1 r2); auto.
    destruct (classic (r1 = r2)).
    + rewrite H4 in H2. elim H2. apply Leq_P1; auto.
    + elim H1. split; auto.
  - intro. destruct H2. elim H3; apply Leq_P2; auto.
Qed.

(* 定理2.5 保不等式性 *)
Theorem Theorem2_5 : ∀ x y, 
  IsSeq x -> IsSeq y -> Convergence x -> Convergence y 
  -> (∃ N0, N0 ∈ ℕ /\ ∀ n, n ∈ ℕ -> N0 < n -> x[n] ≤ y[n]) -> lim x ≤ lim y.
Proof.
  intros. destruct H1 as [a [Ha]], H2 as [b [Hb]].
  destruct H as [H []], H0 as [H0 []].
  assert (∀ε, ε ∈ ℝ /\ 0 < ε -> a < b + (ε + ε)).
  { intros. pose proof H8 as []; destruct H10. destruct H3 as [N0 [Hc Hd]].
    apply H1 in H8 as He; destruct He as [N1 [He Hf]].
    apply H2 in H8 as Hg; destruct Hg as [N2 [Hg Hh]].
    destruct (Max_nat_3 N0 N1 N2) as [N [Hi [Hj [Hk Hl]]]]; auto.
    assert (x[N] ∈ ℝ).
    { apply H5, (@ Property_ran N), Property_Value; auto. rewrite H4; auto. }
    assert (y[N] ∈ ℝ).
    { apply H7, (@ Property_ran N), Property_Value; auto; rewrite H6; auto. }
    apply Hd in Hj; apply Hf in Hk; apply Hh in Hl; auto.
    destruct Hk, Hl. apply Abs_P4 in H13 as [], H15 as []; auto with real.
    apply (Plus_Leq _ _ a) in H13; auto with real.
    rewrite <-Plus_P3, (Plus_P4 (-(a))), Plus_neg2, Plus_P1, Plus_P4 in H13;
    auto with real.
    apply (Plus_Leq _ _ b) in H18; auto with real.
    rewrite <-Plus_P3, (Plus_P4 (-(b))), Plus_neg2, Plus_P1, Plus_P4 in H18; 
    auto with real.
    assert (a - ε < b + ε).
    { split. apply (Leq_P3 _ x[N] _); auto with real; 
      apply (Leq_P3 _ y[N] _); auto with real. intro.
      assert (a - ε ≤ x[N]); auto. rewrite H19 in H20.
      assert (b + ε ≤ y[N]). { apply (Leq_P3 _ x[N] _); auto with real. }
      assert (y[N] = b + ε). { apply Leq_P2; auto with real. }
      rewrite H22 in H16. rewrite (Plus_P4 b), <-Plus_P3, 
      Plus_neg2, Plus_P1 in H16; auto with real. elim H16.
      apply me_zero_Abs; auto. }
    destruct H19. apply (Plus_Leq _ _ ε) in H19; auto with real.
    rewrite <-Plus_P3, (Plus_P4 (-(ε))), Plus_neg2, Plus_P1, <-Plus_P3 in H19;
    auto with real. split; auto; intro. rewrite H21 in H20.
    elim H20. apply (RPlus_eq' _ _ ε); auto with real.
    rewrite <-Plus_P3, (Plus_P4 (-(ε))), Plus_neg2, Plus_P1; auto with real.
    rewrite Plus_P3; auto. }
  pose proof H1; pose proof H2; destruct H1; destruct H2.
  apply Lim_getValue in H9; auto; apply Lim_getValue in H10; auto.
  rewrite H9; rewrite H10. apply NNPP; intro. apply Rnot_le_gt in H13; auto.
  destruct H13. apply (Plus_Leq _ _ a) in H13 as H15; auto.
  assert (b + a ≤ a + a); auto.
  assert (0 < (1 + 1)) as Hm.
  { apply (Order_Co2 _ 1); auto with real.
    left; split; New OrderPM_Co9; auto.
    apply (OrderPM_Co1 _ _ 1) in H17; auto with real.
    rewrite Plus_P4, Plus_P1 in H17; auto with real. destruct H17; auto. }
  assert (0 < ((1 + 1)⁻)) as Hn. { apply OrderPM_Co10; auto with real. }
  assert ((1 + 1) ∈ (ℝ ~ [0])) as Ho.
  { apply MKT4'; split; auto with real.
    apply AxiomII; split; eauto with real.
    intro. apply MKT41 in H17; eauto with real.
    rewrite H17 in Hm; destruct Hm; contradiction. }
  assert ((1 + 1) ⁻ ∈ (ℝ ~ [0])) as Hp. { apply Mult_inv1; auto. }
  assert (a · (1 + 1) = a + a).
  { rewrite Mult_P4, Mult_P5, Mult_P4, Mult_P1; auto with real. } 
  assert (b = b · (1 + 1) - b).
  { assert (b · (1 + 1) = b + b).
    { rewrite Mult_P4, Mult_P5, Mult_P4, Mult_P1; auto with real. }
    rewrite H18. rewrite <-Plus_P3, Plus_neg2, Plus_P1; auto with real. }
  assert (0 < (a - b)) as Hq.
  { apply (Plus_Leq _ _ (-(b))) in H13; auto with real.
    rewrite Plus_neg2 in H13; auto. split; auto; intro. elim H14.
    apply (RPlus_eq' _ _ (-(b))); auto with real. rewrite Plus_neg2; auto. }
  pose proof Hp. apply MKT4' in H19 as [H19 H20]. pose proof Hn; destruct H21.
  rewrite <-H17, H18, <-Plus_P3, (Plus_P4 (-(b))) in H16; auto with real.
  apply (OrderPM_Co7b _ _ ((1 + 1)⁻)) in H16; auto with real. 
  rewrite <-Mult_P3, Divide_P1, Mult_P1 in H16; auto with real. 
  rewrite Mult_P5, <-Mult_P3, Divide_P1, Mult_P1 in H16; auto with real.
  assert (((a - b)· (1 + 1)⁻)· (1 + 1)⁻ ∈ ℝ 
    /\ 0 < ((a - b)· (1 + 1)⁻) · ((1 + 1)⁻)).
  { split.
    - apply Mult_close; auto. apply Mult_close; auto with real.
    - apply OrderPM_Co5; auto with real. left; split; auto.
      apply OrderPM_Co5; auto with real. }
  apply H8 in H23. rewrite <-Mult_P5, <-Mult_P5 in H23; auto with real.
  assert (a < b + ((((a - b) + (a - b)) · ((1 + 1)⁻)) · ((1 + 1)⁻))); auto.
  assert ((a - b) + (a - b) = (a - b) · (1 + 1)).
  { rewrite Mult_P4, Mult_P5, Mult_P4, Mult_P1; auto with real. }
  assert ((a - b) · (1 + 1) /  (1 + 1) = a - b).
  { rewrite <-Mult_P3, Divide_P1, Mult_P1; auto with real. }
  assert (b + (a - b) / (1 + 1) ∈ ℝ). { apply Plus_close; auto with real. }
  rewrite H25, H26 in H24. apply Rnot_lt_ge in H24; auto.
Qed.

Theorem Theorem2_5_1 : ∀ x x0 a, IsSeq x -> x0 ∈ ℝ -> a ∈ ℝ 
  -> Limit_Seq x x0 -> (∃ N0, N0 ∈ ℕ /\ ∀ n, n ∈ ℕ -> N0 < n -> a ≤ x[n])
  -> a ≤ x0.
Proof.
  intros. destruct H3 as [N0 []].
  assert (∃ y, y = \{\ λ u v, u ∈ ℕ /\ v ∈ ℝ /\ v = a \}\) as [y].
  { exists \{\ λ u v, u ∈ ℕ /\ v ∈ ℝ /\ v = a \}\; auto. }
  assert (IsSeq y).
  { repeat split.
    - unfold Relation; intros. rewrite H5 in H6.
      apply AxiomII in H6 as [_[u [v]]]. exists u, v; tauto.
    - intros. rewrite H5 in H6, H7. apply AxiomII' in H6 as [_[H6 []]].
      apply AxiomII' in H7 as [_[_[]]]. rewrite H10; auto.
    - apply AxiomI; split; intros.
      + apply AxiomII in H6 as [H6 []]. rewrite H5 in H7.
        apply AxiomII' in H7; tauto.
      + apply AxiomII; split; eauto. exists a. rewrite H5.
        apply AxiomII'; split; auto. apply MKT49a; eauto.
    - unfold Included; intros. apply AxiomII in H6 as [_[]].
      rewrite H5 in H6. apply AxiomII' in H6; tauto. }
  assert (∀ n, n ∈ ℕ -> a = y[n]).
  { intros. destruct H6 as [H6 []]. apply Property_Fun; auto.
    rewrite H5. apply AxiomII'; split; auto. apply MKT49a; eauto. }
  assert (Limit_Seq y a).
  { unfold Limit_Seq; split; auto. intros. destruct H8.
    exists 1; split; auto with real. intros. apply H7 in H10 as H12.
    rewrite <-H12, Plus_neg2, me_zero_Abs; auto with real.
    apply Leq_P1; auto with real. }
  apply Lim_getValue in H2 as Ha; apply Lim_getValue in H8 as Hb; auto.
  rewrite <-Ha, <-Hb. apply Theorem2_5; auto; try intro.
  - exists a; split; auto.
  - exists x0; split; auto.
  - exists N0; split; auto; intros. apply H4 in H10; auto. rewrite <-H7; auto.
Qed.

Theorem Theorem2_5_2 : ∀ x x0 a, IsSeq x -> x0 ∈ ℝ -> a ∈ ℝ
  -> Limit_Seq x x0 -> (∃ N0, N0 ∈ ℕ /\ ∀ n, n ∈ ℕ -> N0 < n -> x[n] ≤ a)
  -> x0 ≤ a.
Proof.
  intros. destruct H3 as [N0 []].
  assert (∃ y, y = \{\ λ u v, u ∈ ℕ /\ v ∈ ℝ /\ v = a \}\) as [y].
  { exists \{\ λ u v, u ∈ ℕ /\ v ∈ ℝ /\ v = a \}\; auto. }
  assert (IsSeq y).
  { repeat split.
    - unfold Relation; intros. rewrite H5 in H6.
      apply AxiomII in H6 as [_[u [v]]]; exists u, v; tauto.
    - intros. rewrite H5 in H6, H7. apply AxiomII' in H6 as [_[H6 []]];
      apply AxiomII' in H7 as [_[_[]]]. rewrite H10; auto.
    - apply AxiomI; split; intros.
      + apply AxiomII in H6 as [_[]]. rewrite H5 in H6.
        apply AxiomII' in H6; tauto.
      + apply AxiomII; split; eauto. exists a; rewrite H5.
        apply AxiomII'; split; auto. apply MKT49a; eauto.
    - unfold Included; intros. apply AxiomII in H6 as [_[]].
      rewrite H5 in H6; apply AxiomII' in H6; tauto. }
  assert (∀ n, n ∈ ℕ -> a = y[n]).
  { intros. destruct H6 as [H6 []]. apply Property_Fun; auto. rewrite H5.
    apply AxiomII'; split; auto. apply MKT49a; eauto. }
  assert (Limit_Seq y a).
  { split; auto; intros. destruct H8. exists 1; split; auto with real.
    intros. apply H7 in H10 as H12. rewrite <-H12, Plus_neg2; auto.
    rewrite me_zero_Abs; auto with real. apply Leq_P1; auto with real. }
  apply Lim_getValue in H2 as Ha; apply Lim_getValue in H8 as Hb; auto.
  rewrite <-Ha, <-Hb. apply Theorem2_5; auto; try intro.
  - exists x0; split; auto.
  - exists a; split; auto.
  - exists N0; split; auto. intros. apply H4 in H10; auto. rewrite <-H7; auto.
Qed.

Corollary Ntrans : ∀ x y z, x ∈ ℕ -> y ∈ ℕ -> z ∈ ℕ -> x < y -> y < z -> x < z.
Proof.
  intros. apply Nat_P4 in H2, H3; auto with real.
  assert (y ≤ y + 1).
  { apply Nat_P4b; auto. apply Leq_P1; auto with real. }
  assert (x + 1 ≤ z).
  { apply (Leq_P3 _ y _); auto with real.
    apply (Leq_P3 _ (y + 1) _); auto with real. }
  apply Nat_P4a in H5; auto.
Qed.

(* 定理2.6 迫敛性 *)
Theorem Theorem2_6 : ∀ x y z a, IsSeq x -> IsSeq y -> a ∈ ℝ
  -> Limit_Seq x a -> Limit_Seq y a -> IsSeq z
  -> (∃ N0, N0 ∈ ℕ /\ ∀ n, n ∈ ℕ -> N0 < n -> (x[n] ≤ z[n] /\ z[n] ≤ y[n]))
  -> Limit_Seq z a.
Proof.
  split; auto; intros. destruct H2 as [Ha Hb], H3 as [Hc Hd].
  destruct Ha as [Ha []], Hc as [Hc []]. pose proof H6 as [He Hf]; destruct Hf.
  apply Hb in H6 as Hg; apply Hd in H6 as Hh.
  destruct H5 as [N0 [H5]], Hg as [N1 [Hg]], Hh as [N2 [Hh]].
  pose proof (Max_nat_3 _ _ _ H5 Hg Hh) as [N [Hi [Hj [Hk Hl]]]].
  exists N; split; auto; intros. apply (Ntrans _ _ n) in Hj; auto;
  apply (Ntrans _ _ n) in Hk; auto; apply (Ntrans _ _ n) in Hl; auto.
  assert (x[n] ∈ ℝ) as Hm.
  { apply H3, (@ Property_ran n), Property_Value; auto. rewrite H2; auto. } 
  assert (y[n] ∈ ℝ) as Hn.
  { apply H8, (@ Property_ran n), Property_Value; auto. rewrite H7; auto. }
  assert (z[n] ∈ ℝ) as Ho.
  { destruct H4. destruct H16 as [].
    apply H17, (@ Property_ran n), Property_Value; auto. rewrite H16; auto. }
  apply H11 in Hj as []; apply H12 in Hk; apply H13 in Hl; auto.
  destruct Hk, Hl. apply Abs_P4 in H18 as [], H20 as []; auto with real.
  apply (Plus_Leq _ _ a) in H18; auto with real.
  rewrite <-Plus_P3,(Plus_P4 (-(a))),Plus_neg2,Plus_P1 in H18; auto with real.
  apply (Plus_Leq _ _ a) in H23; auto with real.
  rewrite <-Plus_P3,(Plus_P4 (-(a))),Plus_neg2,Plus_P1 in H23; auto with real.
  split. apply Abs_P4; auto with real. split.
  - apply (Leq_P3 _ _ (z[n])) in H18; auto with real.
    apply (Plus_Leq _ _ (-(a))) in H18; auto with real.
    rewrite <-Plus_P3, Minus_P1, Plus_P1 in H18; auto with real.
  - apply (Leq_P3 (z[n]) _ _) in H23; auto with real.
    apply (Plus_Leq _ _ (-(a))) in H23; auto with real.
    rewrite <-Plus_P3, Minus_P1, Plus_P1 in H23; auto with real.
  - intro. destruct (Leq_P4 (z[n] - a) 0); auto with real.
    + rewrite le_zero_Abs, Minus_P3, Minus_P4 in H24; auto with real.
      rewrite <-H24, Minus_P3, Minus_P4, <-Plus_P3, (Plus_P4 (-(a))),
      Plus_neg2, Plus_P1 in H18; auto with real. 
      assert (x[n] = z[n]). { apply Leq_P2; auto. }
      elim H19. rewrite H26, <-H24.
      assert (- z[n] + a = - (z[n] - a)).
      { rewrite Minus_P3, Minus_P4; auto with real. }
      rewrite H27; apply le_zero_Abs; auto with real.
    + rewrite me_zero_Abs in H24; auto with real.
      rewrite <-H24, <-Plus_P3, (Plus_P4 (-(a))), Plus_neg2, Plus_P1 in H23;
      auto with real. assert (y[n] = z[n]). { apply Leq_P2; auto. }
      elim H21. rewrite H26, <-H24. apply me_zero_Abs; auto with real.
Qed.

(* 定理2.7 四则运算法则 *)
(* x,y是收敛数列,则 x+y 收敛,且有 lim(x+y) = lim x + lim y *)
Theorem Theorem2_7_1 : ∀ x y, IsSeq x -> IsSeq y 
  -> Convergence x -> Convergence y
  -> Convergence (\{\ λ n v, n ∈ ℕ /\ v ∈ ℝ /\ v = x[n] + y[n] \}\)
    /\ lim \{\ λ n v, n ∈ ℕ /\ v ∈ ℝ /\ v = x[n] + y[n] \}\ = lim x + lim y.
Proof.
  intros. destruct H1 as [a [Ha]], H2 as [b [Hb]].
  assert (∀ ε, ε ∈ ℝ /\ 0 < ε -> (∃ N, N ∈ ℕ /\ ∀ n, n ∈ ℕ -> N < n
    -> ｜((x[n] + y[n]) - (a + b))｜ < ε + ε)).
  { intros. destruct H1 as [], H2 as []. apply H4 in H3 as Hc;
    apply H5 in H3 as Hd. destruct Hc as [N1 []], Hd as [N2 []].
    pose proof (Max_nat_2 _ _ H6 H8) as [N [H12 []]]. exists N; split; auto.
    intros. apply (Ntrans _ _ n) in H10; apply (Ntrans _ _ n) in H11; auto.
    apply H7 in H10; apply H9 in H11; auto. pose proof H3 as [He []]. 
    assert (x[n] ∈ ℝ /\ y[n] ∈ ℝ) as [].
    { destruct H as [H []], H0 as [H0 []]. split;
      [apply H18, (@ Property_ran n), Property_Value; auto; rewrite H17; auto|
      apply H20, (@ Property_ran n), Property_Value; auto; rewrite H19; auto]. }
    assert (｜(x[n] - a)｜ + ｜(y[n] - b)｜ < ε + ε).
    { destruct H10. apply OrderPM_Co4; auto with real. }
    assert ((x[n] + y[n]) - (a + b) = x[n] - a + (y[n] - b)).
    { rewrite Minus_P3, (Plus_P4 (- a)), <-Plus_P3, (Plus_P3 y[n]),
      (Plus_P4 _ (- a)), Plus_P3; auto with real. }
    rewrite H20. assert ((x[n] - a) ∈ ℝ /\ (y[n] - b) ∈ ℝ) as [].
    { split; auto with real. }
    pose proof (Abs_P5 (x[n] - a) (y[n] - b) H21 H22) as [Hf [_ _]].
    apply (Order_Co2 _ (｜(x[n] - a)｜ + ｜(y[n] - b)｜) _); auto with real. }
  assert (Limit_Seq \{\ λ n v, n ∈ ℕ /\ v ∈ ℝ /\ v = x[n] + y[n] \}\ (a + b)).
  { assert (IsSeq \{\ λ n v, n ∈ ℕ /\ v ∈ ℝ /\ v = x[n] + y[n] \}\).
    { repeat split.
      - unfold Relation; intros. apply AxiomII in H4 as [_[x0 [y0]]].
        exists x0, y0; tauto.
      - intros. apply AxiomII' in H4 as [_[H4 []]]; 
        apply AxiomII' in H5 as [_[_[]]]. rewrite H8; auto.
      - apply AxiomI; split; intros.
        + apply AxiomII in H4 as [H4 [y0]]. apply AxiomII' in H5; tauto.
        + destruct H as [H []], H0 as [H0 []].
          assert ((x[z] + y[z]) ∈ ℝ).
          { apply Plus_close; [apply H6, (@ Property_ran z), Property_Value;
            auto; rewrite H5; auto|apply H8, (@ Property_ran z),
            Property_Value; auto; rewrite H7; auto]. }
          apply AxiomII; split; eauto. exists (x[z] + y[z]).
          apply AxiomII'; repeat split; auto. apply MKT49a; eauto.
      - unfold Included; intros. apply AxiomII in H4 as [_[]].
        apply AxiomII' in H4; tauto. }
    split; auto; intros. pose proof H5 as [].
    pose proof OrderPM_Co9; pose proof H8 as [].
    assert (0 < 1 + 1).
    { apply (Order_Co2 _ 1 _); auto with real. left; split; auto. 
      apply (Plus_Leq _ _ 1) in H9; auto with real. rewrite Plus_P4,
      Plus_P1 in H9; auto with real. }
    assert (0 < ((1 + 1)⁻)). { apply OrderPM_Co10; auto with real. }
    assert ((1 + 1) ∈ (ℝ ~ [0])). 
    { assert ((1 + 1) ∈ ℝ). { auto with real. }
      apply AxiomII; repeat split; eauto. apply AxiomII; split; eauto.
      intro. apply MKT41 in H14; eauto with real. rewrite H14 in H11.
      destruct H11; eauto. }
    apply Mult_inv1 in H13 as Hg. apply AxiomII in Hg as [_[Hh]].
    assert (ε + ε = ε · (1 + 1)).
    { rewrite Mult_P4, Mult_P5, Mult_P4, Mult_P1; auto with real. }
    assert (0 < (ε / (1 + 1))).
    { apply (OrderPM_Co7a _ _ ((1 + 1)⁻)) in H7; auto with real.
      rewrite Mult_P4, PlusMult_Co1 in H7; auto with real. }
    assert ((ε / (1 + 1)) ∈ ℝ /\ 0 < (ε / (1 + 1))).
    { split; auto. apply Mult_close; auto. }
    apply H3 in H17. destruct H17 as [N []]. exists N; split; auto.
    intros. apply H18 in H20; auto. rewrite <-Mult_P5 in H20; auto.
    (* ****** rewrite H15 in H20. ****** *)
    assert (｜(x[n] + y[n] - (a + b))｜ < ((ε + ε) · ((1 + 1)⁻))); auto.
    rewrite H15, <-Mult_P3, Divide_P1, Mult_P1 in H21; auto with real.
    assert (x[n] + y[n] ∈ ℝ).
    { destruct H as [H []], H0 as [H0 []]. apply Plus_close;
      [apply H23, (@ Property_ran n), Property_Value; auto; rewrite H22; auto|
      apply H25, (@ Property_ran n), Property_Value; auto; rewrite H24; auto]. }
    assert (x[n] + y[n] = \{\ λ n v, n ∈ ℕ /\ v ∈ ℝ /\ v = x[n] + y[n] \}\[n]).
    { destruct H4 as [H4 []]. apply Property_Fun; auto.
      apply AxiomII'; repeat split; auto. apply MKT49a; eauto with real. }
    rewrite <-H23; auto. }
  pose proof H4; destruct H5. split.
  - exists (a + b); split; auto with real.
  - apply Lim_getValue in H1, H2, H4; auto with real. rewrite H1, H2, H4; auto.
Qed.

(* x,y是收敛数列,则 x-y 收敛,且有 lim(x-y) = limx-limy *)
Theorem Theorem2_7_2 : ∀ x y, IsSeq x -> IsSeq y 
  -> Convergence x -> Convergence y
  -> Convergence (\{\ λ n v, n ∈ ℕ /\ v ∈ ℝ /\ v = x[n] - y[n] \}\)
    /\ lim \{\ λ n v, n ∈ ℕ /\ v ∈ ℝ /\ v = x[n] - y[n] \}\ = lim x - lim y.
Proof.
  intros. pose proof H1 as Hz. 
  set (y' := \{\ λ n v, n ∈ ℕ /\ v ∈ ℝ /\ v = - y[n] \}\).
  assert (Function y') as Ha.
  { split; intros.
    - unfold Relation; intros. apply AxiomII in H3 as [_[x0 [y0]]].
      exists x0, y0; tauto.
    - apply AxiomII' in H3 as [_[H3 [H5]]], H4 as [_[_ [H4]]].
      rewrite H7; auto. }
  assert (∀ n, n ∈ ℕ -> - y[n] = y'[n]) as Hb.
  { destruct H0 as [H0 []]; intros. assert (- y[n] ∈ ℝ).
    { apply Plus_neg1a, H4, (@ Property_ran n), Property_Value; auto;
      rewrite H3; auto. }
    apply Property_Fun; auto. apply AxiomII'; repeat split; auto.
    apply MKT49a; eauto. }
  assert (IsSeq y') as Hc.
  { split; auto; split.
    - apply AxiomI; split; intros.
      + apply AxiomII in H3 as []. destruct H4 as [y0].
        apply AxiomII' in H4; tauto.
      + apply Hb in H3 as H4. assert (y'[z] ∈ ℝ).
        { destruct H0 as [H0 []]. rewrite <-H4. apply Plus_neg1a, H6, 
          (@ Property_ran z), Property_Value; auto; rewrite H5; auto. }
        apply AxiomII; split; eauto. exists y'[z].
        apply AxiomII'; repeat split; auto. apply MKT49a; eauto.
    - unfold Included; intros. apply AxiomII in H3 as [_[x0]].
      apply AxiomII' in H3; tauto. }
  assert (\{\ λ n v, n ∈ ℕ /\ v ∈ ℝ /\ v = x[n] - y[n] \}\
    = \{\ λ n v, n ∈ ℕ /\ v ∈ ℝ /\ v = x[n] + y'[n] \}\) as Hd.
  { apply AxiomI; split; intros.
    - apply AxiomII in H3 as [H3 [x0 [y0 [H4 [H5 []]]]]];
      apply AxiomII; split; auto. exists x0, y0; repeat split; auto.
      apply Hb in H5. rewrite <-H5; auto.
    - apply AxiomII in H3 as [H3 [x0 [y0 [H4 [H5 []]]]]];
      apply AxiomII; split; auto. exists x0, y0; repeat split; auto.
      apply Hb in H5. rewrite H5; auto. }
  destruct H1 as [a [Hf Hg]]; apply Lim_getValue in Hg as Hh; auto. 
  destruct H2 as [b [Hi Hj]]; apply Lim_getValue in Hj as Hk; auto.
  assert (Limit_Seq y' (-b)).
  { split; auto; intros. destruct Hj. apply H3 in H1 as [N []].
    exists N; split; auto; intros. rewrite Minus_P4; auto.
    apply H4 in H6; auto. apply Hb in H5 as H7.
    assert (y'[n] ∈ ℝ).
    { destruct Hc as [Hc []]. apply H9, (@ Property_ran n), Property_Value;
      auto. rewrite H8; auto. }
    assert (y[n] ∈ ℝ).
    { destruct H2 as [H2 []]. apply H10, (@ Property_ran n), Property_Value;
      auto; rewrite H9; auto. }
    apply (RMult_eq _ _ (-(1))) in H7; auto with real.
    rewrite Mult_P4, <-PlusMult_Co3, Minus_P4, Mult_P4, <-PlusMult_Co3 in H7;
    auto with real. rewrite H7, PlusMult_Co3, Mult_P4 in H6; auto with real.
    assert (- b = b · (-(1))).
    { rewrite PlusMult_Co3, Mult_P4; auto with real. }
    rewrite H10, <-Mult_P5, Mult_P4, <-PlusMult_Co3 in H6; auto with real.
    assert ((y'[n] + b) ∈ ℝ). { auto with real. }
    assert (｜(y'[n] + b)｜ = ｜(- (y'[n] + b))｜). { apply Abs_P2; auto. }
    rewrite H12; auto. }
  apply Lim_getValue in H1 as Hl; auto with real.
  assert (lim y' = - lim y). { rewrite Hl, Hk; auto. }
  assert (Convergence y').
  { exists (- b); split; auto with real. }
  rewrite Hd, <-H2. apply Theorem2_7_1; auto.
Qed.

Corollary RMult_le_0_lt_compat : ∀ r1 r2 r3 r4, r1 ∈ ℝ -> r2 ∈ ℝ 
  -> r3 ∈ ℝ -> r4 ∈ ℝ -> 0 ≤ r1 -> 0 ≤ r3 -> r1 < r2 -> r3 < r4 
  -> r1 · r3 < r2 · r4.
Proof.
  intros. destruct (classic (r3 = 0)).
  - rewrite H7, PlusMult_Co1; auto. apply OrderPM_Co5; auto. 
    left; split; [apply (Order_Co2 _ r1 _); auto with real|
    apply (Order_Co2 _ r3 _); auto with real].
  - assert (0 < r3). { split; auto. }
    assert (0 < r2). { apply (Order_Co2 _ r1 _); auto with real. }
    apply (OrderPM_Co7a _ _ r3) in H5; auto.
    apply (OrderPM_Co7a _ _ r2) in H6; auto.
    rewrite Mult_P4, (Mult_P4 r4) in H6; auto.
    destruct H5; apply (Order_Co2 _ (r2 · r3) _); auto with real.
Qed.

(* x,y是收敛数列,则 x*y 收敛,且有 lim(x*y) = limx*limy *)
Theorem Theorem2_7_3 : ∀ x y, IsSeq x -> IsSeq y 
  -> Convergence x -> Convergence y
  -> Convergence \{\ λ n v, n ∈ ℕ /\ v ∈ ℝ /\ v = x[n] · y[n] \}\
    /\ lim \{\ λ n v, n ∈ ℕ /\ v ∈ ℝ /\ v = x[n] · y[n] \}\ = lim x · lim y.
Proof.
  intros. pose proof H1; pose proof H2.
  destruct H3 as [a [Ha Hb]], H4 as [b [Hc Hd]].
  pose proof (Theorem2_3 _ H0 H2) as [M [He [Hf]]].
  pose proof H; pose proof H0. destruct H4 as [H4 []], H5 as [H5 []].
  assert (∀ ε, ε ∈ ℝ /\ 0 < ε -> (∃ N, N ∈ ℕ /\ ∀ n, n ∈ ℕ -> N < n 
    -> ｜((x[n] · y[n]) - (a · b))｜ < (M + ｜a｜) · ε)).
  { intros. apply Hb in H10 as Hg; destruct Hg as [N1 []].
    apply Hd in H10 as Hh; destruct Hh as [N2 []].
    pose proof (Max_nat_2 _ _ H11 H13) as [N [H15 []]].
    exists N; split; auto; intros. pose proof H10; destruct H20 as [Hh Hi]. 
    assert (N1 < n /\ N2 < n) as [].
    { split; [apply Ntrans with N; auto|apply Ntrans with N; auto]. }
    apply H12 in H20; apply H14 in H21; auto.
    assert (x[n] ∈ ℝ /\ y[n] ∈ ℝ) as [].
    { split; [apply H7, (@ Property_ran n), Property_Value; auto; 
      rewrite H6; auto| apply H9, (@ Property_ran n), Property_Value; auto;
      rewrite H8; auto]. }
    assert ((x[n] · y[n]) - (a · b) = (x[n] - a) · y[n] + a · (y[n] - b)).
    { assert (a · (y[n] - b) = a · y[n] - a · b).
      { rewrite Mult_P4, Mult_P5, Mult_P4, PlusMult_Co3, <-Mult_P3, 
        (Mult_P4 b), <-PlusMult_Co3; auto with real. }
      rewrite Mult_P5, H24, <-Plus_P3, (Plus_P3 ((-(a)) · y[n])),
      (Plus_P4 ((-(a)) · y[n])); auto with real.
      assert (((-(a)) · y[n]) = - (a · y[n])). 
      { rewrite PlusMult_Co3, <-Mult_P3, <-PlusMult_Co3; auto with real. }
      rewrite H25, Minus_P1, (Plus_P4 0), Plus_P1; auto with real. }
    rewrite H24. assert (｜((x[n] - a) · y[n] + a · (y[n] - b))｜
      ≤ ｜((x[n] - a) · y[n])｜ + ｜(a · (y[n] - b))｜).
    { apply Abs_P5; auto with real. }
    apply (Order_Co2 _ (｜((x[n] - a) · y[n])｜ + ｜(a · (y[n] - b))｜) _);
    auto with real. apply Abs_in_R; auto with real. apply Plus_close;
    auto with real. right; split; auto. rewrite (Mult_P5 M); auto with real.
    assert (｜((x[n] - a) · y[n])｜ = ｜(x[n] - a)｜· ｜(y[n])｜).
    { apply Abs_P3; auto with real. }
    assert (｜(a · (y [n] - b))｜ = ｜a｜· ｜(y[n] - b)｜).
    { apply Abs_P3; auto with real. }
    rewrite H26, H27.
    assert (｜(x[n] - a)｜· ｜(y[n])｜ < M · ε).
    { assert (0 ≤ ｜(x[n] - a)｜). { apply Abs_P1; auto with real. }
      assert (0 ≤ ｜(y[n])｜). { apply Abs_P1; auto. }
      rewrite (Mult_P4 M); auto. destruct (classic (｜(y[n])｜ = M)).
      - rewrite H30. apply OrderPM_Co7a; auto with real.
      - assert (｜(y[n])｜ < M). { apply H3 in H18; split; auto. }
        apply RMult_le_0_lt_compat; auto with real. }
    assert (｜a｜ · ｜(y [n] - b)｜ ≤ ｜a｜ · ε).
    { assert (0 ≤ ｜a｜). { apply Abs_P1; auto. }
      rewrite Mult_P4, (Mult_P4 (｜a｜)); auto with real.
      destruct H21; apply OrderPM_Co7b; auto with real. }
    rewrite Plus_P4, (Plus_P4 (M · ε)); auto with real.
    apply OrderPM_Co4; auto with real. }
  assert (IsSeq \{\ λ n v, n ∈ ℕ /\ v ∈ ℝ /\ v = x[n] · y[n] \}\).
  { repeat split; intros.
    - unfold Relation; intros. apply AxiomII in H11 as [_[x0 [y0]]].
      exists x0, y0; tauto.
    - apply AxiomII' in H11 as [_[H11 []]]; 
      apply AxiomII' in H12 as [_[_[H12]]]. rewrite H15; auto.
    - apply AxiomI; split; intros.
      + apply AxiomII in H11 as [_[y0]]. apply AxiomII' in H11; tauto.
      + assert (x[z] · y[z] ∈ ℝ).
        { apply Mult_close; [apply H7, (@ Property_ran z), Property_Value;
          auto; rewrite H6; auto|apply H9, (@ Property_ran z), Property_Value;
          auto; rewrite H8; auto]. } 
        apply AxiomII; split; eauto. exists (x[z] · y[z]); apply AxiomII';
        split; auto. apply MKT49a; eauto.
    - unfold Included; intros. apply AxiomII in H11 as [_[x0]].
      apply AxiomII' in H11; tauto. }
  assert (Limit_Seq \{\ λ n v, n ∈ ℕ /\ v ∈ ℝ /\ v = x[n] · y[n] \}\ (a · b)).
  { split; auto; intros. assert (0 < (M + ｜a｜)).
    { assert (M ≤ (M + ｜a｜)).
      { assert (M + 0 ≤ M + ｜a｜).
        { apply OrderPM_Co3; auto with real. apply Leq_P1; auto.
          apply Abs_P1; auto. }
        rewrite Plus_P1 in H13; auto. }
      apply (Order_Co2 _ M _); auto with real. }
    assert ((M + ｜a｜) ∈ (ℝ ~ [0])).
    { apply MKT4'; split; auto with real.
      apply AxiomII; split; eauto with real. intro. apply MKT41 in H14;
      eauto with real. rewrite H14 in H13. destruct H13; auto. }
    destruct H12. apply Mult_inv1 in H14 as H16. apply MKT4' in H16 as [].
    apply OrderPM_Co10 in H13; auto with real.
    apply (OrderPM_Co7a _ _ ε) in H13; auto with real.
    rewrite Mult_P4, PlusMult_Co1 in H13; auto with real.
    assert ((((M + ｜a｜)⁻) · ε) ∈ ℝ /\ 0 < (((M + ｜a｜)⁻) · ε)).
    { split; auto with real. }
    apply H10 in H18 as [N [H18]]; exists N; split; auto. intros.
    rewrite Mult_P3, Divide_P1, (Mult_P4 1), Mult_P1 in H19; auto with real.
    assert (x[n] · y[n] = 
      \{\ λ n v, n ∈ ℕ /\ v ∈ ℝ /\ v = x[n] · y[n] \}\ [n]).
    { assert (x[n] · y[n] ∈ ℝ).
      { apply Mult_close; [apply H7, (@ Property_ran n), Property_Value;
        auto; rewrite H6; auto|apply H9, (@ Property_ran n), Property_Value;
        auto; rewrite H8; auto]. }
      apply Property_Fun. destruct H11; auto.
      apply AxiomII'; repeat split; auto. apply MKT49a; eauto with real. }
    apply H19 in H21; auto. rewrite <-H22; auto. }
  split. exists (a · b); split; auto with real.
  apply Lim_getValue in Hb, Hd; auto. rewrite Hb, Hd.
  apply Lim_getValue in H12; auto with real.
Qed.

Proposition Abs_neq_0 : ∀ x, x ∈ ℝ -> x ≠ 0 -> 0 ≠｜x｜ .
Proof.
  intros. intro. elim H0. apply Abs_P1; auto.
Qed.

Proposition Abs_div : ∀ a b, a ∈ ℝ -> b ∈ ℝ -> b ≠ 0 
  -> ｜(a / b)｜ = ｜a｜ / ｜b｜.
Proof.
  intros. pose proof H; pose proof H0; pose proof OrderPM_Co9.
  assert (b ∈ (ℝ ~ [0])) as Ha.
  { apply MKT4'; split; auto. apply AxiomII; split; eauto. intro.
    apply MKT41 in H5; eauto with real. }
  assert (- b ∈ (ℝ ~ [0])) as Hb.
  { apply MKT4'; split; auto with real. apply AxiomII; split; eauto with real.
    intro. apply MKT41 in H5; eauto with real. apply (RMult_eq _ _ (-(1)))
    in H5; auto with real. rewrite Mult_P4, <-PlusMult_Co3, Minus_P4,
    Mult_P4, PlusMult_Co1 in H5; auto with real. }
  apply Mult_inv1 in Ha as Hc. apply MKT4' in Hc as [Hc _].
  destruct (Leq_P4 b 0) as [|]; auto with real.
  - assert (((b)⁻) ≤ 0) as Hd.
    { assert (b < 0). { split; auto. }
      destruct (Order_Co1 ((b)⁻) 0) as [H7 |[H7 | H7]]; auto with real.
      -- destruct H7; auto.
      -- apply (OrderPM_Co6 b ((b)⁻)) in H7; auto.
         rewrite Divide_P1 in H7; auto. destruct H7, H4.
         elim H8. apply Leq_P2; auto with real.
      -- rewrite H7; apply Leq_P1; auto with real. }
    destruct (Leq_P4 a 0) as [|]; auto with real.
    + pose proof H6. apply (OrderPM_Co8b _ _ ((b)⁻)) in H7; auto with real.
      rewrite Mult_P4, PlusMult_Co1 in H7; auto with real.
      assert (｜(a · (b ⁻))｜= a · (b ⁻)).
      { apply me_zero_Abs; auto with real. }
      assert ((｜a｜ = - a) /\ (｜b｜ = - b)) as [].
      { split; [apply le_zero_Abs; auto|apply le_zero_Abs; auto]. }
      rewrite H8, H9, H10. apply Mult_Co3; auto with real.
      rewrite PlusMult_Co3, <-Mult_P3, (Mult_P4 a), (Mult_P3 b), Divide_P1,
      (Mult_P4 1), Mult_P1, <-PlusMult_Co3; auto with real.
    + pose proof H6. apply (OrderPM_Co8b _ _ ((b)⁻)) in H7; auto with real.
      rewrite (Mult_P4 0), PlusMult_Co1 in H7; auto with real.
      assert (｜(a · (b ⁻))｜= - (a · (b ⁻))).
      { apply le_zero_Abs; auto with real. }
      assert ((｜a｜ = a) /\ (｜b｜ = - b)) as [].
      { split; [apply me_zero_Abs; auto|apply le_zero_Abs; auto]. }
      rewrite H8, H9, H10. apply Mult_Co3; auto with real.
      rewrite PlusMult_Co3, (Mult_P4 (-(1))), <-Mult_P3, <-PlusMult_Co3,
      Minus_P4; auto with real. rewrite (Mult_P4 a), Mult_P3, Divide_P1,
      Mult_P4, Mult_P1; auto with real.
  - assert (0 < (b ⁻)) as []. { apply OrderPM_Co10; auto; split; auto. }
    destruct (Leq_P4 a 0) as [|]; auto with real.
    + pose proof H8. apply (OrderPM_Co7b _ _ ((b)⁻)) in H9; auto with real.
      rewrite (Mult_P4 0), PlusMult_Co1 in H9; auto with real.
      assert (｜(a · (b ⁻))｜= - (a · (b ⁻))).
      { apply le_zero_Abs; auto with real. }
      assert ((｜a｜ = - a) /\ (｜b｜ = b)) as [].
      { split; [apply le_zero_Abs; auto|apply me_zero_Abs; auto]. }
      rewrite H10, H11, H12. rewrite PlusMult_Co3, Mult_P4; auto with real.
      symmetry. rewrite PlusMult_Co3, <-Mult_P3, Mult_P4; auto with real.
    + pose proof H8; apply (OrderPM_Co7b _ _ ((b)⁻)) in H9; auto with real.
      rewrite Mult_P4, PlusMult_Co1 in H9; auto with real.
      assert (｜(a · (b ⁻))｜= (a · (b ⁻))).
      { apply me_zero_Abs; auto with real. }
      assert ((｜a｜ = a) /\ (｜b｜ = b)) as [].
      { split; [apply me_zero_Abs; auto|apply me_zero_Abs; auto]. }
      rewrite H10, H11, H12; auto.
Qed.

Corollary Rinv_mult_distr : ∀ r1 r2, r1 ∈ (ℝ ~ [0]) -> r2 ∈ (ℝ ~ [0])
  -> (r1 · r2)⁻ = (r1)⁻ · (r2)⁻.
Proof.
  intros. pose proof H; pose proof H0.
  apply MKT4' in H as [H Ha]; apply MKT4' in H0 as [H0 Hb].
  apply Mult_inv1 in H1 as Hc; apply MKT4' in Hc as [Hc _].
  apply Mult_inv1 in H2 as Hd; apply MKT4' in Hd as [Hd _].
  apply AxiomII in Ha as [_ Ha]; apply AxiomII in Hb as [_ Hb].
  assert (r1 · r2 ∈ (ℝ ~ [0])).
  { apply MKT4'; split; auto with real. apply AxiomII; split; eauto with real.
    intro. apply MKT41 in H3; eauto with real.
    elim Ha. apply MKT41; eauto with real. apply (RMult_eq' _ _ r2);
    auto with real. symmetry. rewrite Mult_P4, PlusMult_Co1; auto with real. }
  apply Mult_inv1 in H3; apply MKT4' in H3 as [H3 _].
  assert ((1 / r1) · (1 / r2) = (1 · 1) / (r1 · r2)).
  { apply Frac_P2; auto with real. }
  rewrite (Mult_P4 1), Mult_P1, (Mult_P4 1), Mult_P1 in H4; auto with real.
  rewrite Mult_P1, (Mult_P4 1), Mult_P1 in H4; auto with real.
Qed.

Corollary Rinv_add_cond : ∀ r, r ∈ (ℝ ~ [0]) -> ｜r｜ ∈ (ℝ ~ [0]).
Proof.
  intros. pose proof H. apply MKT4' in H0 as []. apply AxiomII in H1 as [_ H1].
  apply MKT4'; split; auto with real. apply AxiomII; split; eauto with real.
  intro. elim H1. apply MKT41 in H2; eauto with real.
  apply MKT41; eauto with real. apply Abs_P1; auto.
Qed.

Corollary Rlt_trans : ∀ x y z, x ∈ ℝ -> y ∈ ℝ -> z ∈ ℝ 
  -> x < y -> y < z -> x < z.
Proof.
  intros. destruct H2. apply (Order_Co2 _ y _); auto.
Qed.

(* y是收敛数列,y(n),lim y均不等于0,则lim /y[n] = /(lim y)  *)
Theorem Theorem2_7_4' : ∀ y, IsSeq y -> Convergence y
  -> (∀ n, n ∈ ℕ -> y[n] ≠ 0) -> lim y ≠ 0
  -> Limit_Seq (\{\ λ n v, n ∈ ℕ /\ v ∈ ℝ /\ v = (y[n])⁻ \}\) (lim y)⁻.
Proof.
  intros. pose proof H0. destruct H3 as [b [Ha]].
  apply Lim_getValue in H3 as Hb; auto. rewrite Hb in *.
  destruct OrderPM_Co9. pose proof OrderPM_Co9 as Hc.
  assert (0 < 1 + 1) as Hd.
  { apply (Order_Co2 _ 1 _); auto with real. left; split; auto.
    assert (1 + 0 ≤ 1 + 1).
    { apply OrderPM_Co4; auto with real. apply Leq_P1; auto with real. }
    rewrite Plus_P1 in H6; auto with real. }
  apply OrderPM_Co10 in Hd as He; auto with real.
  assert (1 + 1 ∈ (ℝ ~ [0])) as Hf.
  { apply MKT4'; split; auto with real.
    apply AxiomII; split; eauto with real. intro. apply MKT41 in H6;
    eauto with real. rewrite H6 in Hd. destruct Hd; auto. }
  apply Mult_inv1 in Hf as Hg. apply MKT4' in Hg as [Hg Hh].
  assert ((1 / (1 + 1)) < 1) as Hi.
  { assert (1 + 0 < (1 + 1)).
    { apply OrderPM_Co4; auto with real. apply Leq_P1; auto with real. }
    rewrite Plus_P1 in H6; auto with real.
    apply (OrderPM_Co7a _ _ (1 + 1)⁻) in H6; auto with real.
    rewrite Divide_P1 in H6; auto. }
  assert ((-(1)) < 0) as Hz. { apply OrderPM_Co2a; auto with real. }
  assert (b ∈ ((ℝ ~ [0]))) as Hy.
  { apply MKT4'; split; auto. apply AxiomII; split; eauto. intro.
    apply MKT41 in H6; eauto with real. }
  assert (0 < b· b) as Hx.
  { destruct (Leq_P4 b 0); auto with real.
    - assert (b < 0). { split; auto. } apply OrderPM_Co5; auto.
    - assert (0 < b). { split; auto. } apply OrderPM_Co5; auto. }
  assert (b· b ∈ ℝ) as Hw. { auto with real. }
  assert (b· b ∈ (ℝ ~ [0])) as Hv.
  { apply MKT4'; split; auto. apply AxiomII; split; eauto.
    intro. apply MKT41 in H6; eauto with real.
    rewrite H6 in Hx. destruct Hx; auto. }
  apply Mult_inv1 in Hy as Hu; apply MKT4' in Hu as [Hu _].
  apply Mult_inv1 in Hv as Ht. apply MKT4' in Ht as [Ht _].
  assert (∃ N3, N3 ∈ ℕ /\ ∀ n, n ∈ ℕ -> N3 < n -> ｜b｜ / (1 + 1) < ｜(y[n])｜).
  { destruct (Leq_P4 b 0); auto with real.
    - assert (b < 0). { split; auto. }
      assert (b / (1 + 1) ∈ ℝ /\ b / (1 + 1) ∈ ］b,0［).
      { split; auto with real. 
        apply AxiomII. apply (OrderPM_Co8a _ _ b) in Hi; auto with real.
        rewrite Mult_P4, Mult_P1 in Hi; auto with real.
        rewrite Mult_P4, Mult_P3, Mult_P1 in Hi; auto with real.
        apply (OrderPM_Co7a _ _ ((1 + 1)⁻)) in H7; auto with real.
        rewrite (Mult_P4 0), PlusMult_Co1 in H7; auto with real.
        split; eauto with real. }
      assert ((∀ a', a' ∈ ℝ /\ a' ∈ ］b,0［
        -> (∃ N, N ∈ ℕ /\ (∀ n, n ∈ ℕ -> N < n -> y[n] < a')))).
      { apply Theorem2_4_2; auto. }
      apply H9 in H8 as H10. destruct H10 as [N [H10]]. exists N; split; auto.
      intros. apply H11 in H13; auto. destruct H8 as [_]. 
      assert (y[n] ∈ ℝ).
      { destruct H as [H []]. apply H15, (@ Property_ran n), Property_Value;
        auto; rewrite H14; auto. }
      assert (y[n] < 0).
      { apply AxiomII in H8 as [_[_[_]]]. destruct H13.
        apply (Order_Co2 _ (b / (1 + 1)) _); auto with real. }
      destruct H15. assert (｜b｜ = (- b) /\ ｜(y[n])｜ = (-(y[n]))) as [].
      { split; [apply le_zero_Abs; auto|apply le_zero_Abs; auto]. } 
      rewrite H17, H18. apply (OrderPM_Co8a _ _ (-(1))) in H13; auto with real.
      rewrite Mult_P4, (Mult_P4 (y[n])), <-PlusMult_Co3, <-PlusMult_Co3,
      PlusMult_Co3, Mult_P3, <-PlusMult_Co3 in H13; auto with real.
    - assert (0 < b). { split; auto. }
      assert (b / (1 + 1) ∈ ℝ /\ b / (1 + 1) ∈ ］0,b［).
      { split; auto with real.
        apply AxiomII. apply (OrderPM_Co7a _ _ b) in Hi; auto with real.
        rewrite (Mult_P4 1), Mult_P1, Mult_P4, (Mult_P4 1), Mult_P1 in Hi;
        auto with real. apply (OrderPM_Co7a _ _ ((1 + 1)⁻)) in H7;
        auto with real. rewrite Mult_P4, PlusMult_Co1 in H7; auto with real.
        split; eauto with real. }
      assert ((∀ a', a' ∈ ℝ /\ a' ∈ ］0,b［
        -> (∃ N, N ∈ ℕ /\ (∀ n, n ∈ ℕ -> N < n -> a' < y[n])))).
      { apply Theorem2_4_1; auto. }
      apply H9 in H8 as H10. destruct H10 as [N [H10]]. exists N; split; auto.
      intros. apply H11 in H13; auto. destruct H8 as [_].
      assert (y[n] ∈ ℝ).
      { destruct H as [H []]. apply H15, (@ Property_ran n), Property_Value;
        auto; rewrite H14; auto. }
      assert (0 < y[n]).
      { apply AxiomII in H8 as [_[_[H8 _]]]. destruct H8.
        apply (Order_Co2 _ (b / (1 + 1)) _); auto with real. }
      assert (｜b｜ = b /\ ｜(y[n])｜ = (y[n])) as [].
      { destruct H7, H15. split; [apply me_zero_Abs in H7; auto|
        apply me_zero_Abs in H15; auto]. }
      rewrite H16, H17; auto. }
  assert ((∀ ε, ε ∈ ℝ /\ 0 < ε -> (∃ N, N ∈ ℕ /\ ∀ n, n ∈ ℕ -> N < n ->
    ｜((y[n])⁻ - (b)⁻)｜ < (1 + 1) · ε / (b · b)))).
  { intros. pose proof H7 as Hs. destruct Hs as [Hs Hr].
    apply H3 in H7 as [N2 [H7]]. destruct H6 as [N3 [H6]].
    pose proof (Max_nat_2 _ _ H7 H6) as [N [H10 []]]. exists N; split; auto. 
    intros. apply H1 in H13 as Hj.
    assert (N2 < n /\ N3 < n) as [].
    { split; [apply (Ntrans _ N _); auto|apply (Ntrans _ N _); auto]. }
    apply H8 in H15; apply H9 in H16; auto.
    assert (y[n] ∈ ℝ).
    { destruct H as [H []]; apply H18, (@ Property_ran n),Property_Value;
      auto; rewrite H17; auto. }
    assert (y[n] ∈ (ℝ ~ [0])).
    { apply MKT4'; split; auto. apply AxiomII; split; eauto. intro.
      apply MKT41 in H18; eauto with real. }
    apply Mult_inv1 in H18 as Hq; apply MKT4' in Hq as [Hq _].
    assert ((y [n] · b) ∈ ℝ). { auto with real. }
    assert ((y [n] · b) ∈ (ℝ ~ [0])).
    { apply MKT4'; split; auto. apply AxiomII; split; eauto.
      intro. apply MKT41 in H20; eauto with real.
      apply PlusMult_Co2 in H20 as [|]; auto. }
    apply Mult_inv1 in H20 as Hp. apply MKT4' in Hp as [Hp _].
    assert ((1 / y[n]) - (1 / b) = -((y[n] - b) / (y[n] · b))).
    { assert ((1 / y[n]) = (b / (y[n] · b))).
      { assert ((1 / y[n]) = ((1· b) / (y[n] · b))).
        { apply Frac_P1; auto with real. }
        symmetry in H21. rewrite (Mult_P4 1), Mult_P1 in H21; auto with real. }
      assert (1 / b = (y[n] / (y[n] · b))).
      { assert (1 / b = ((1 · y[n]) / (b· y[n]))).
        { apply Frac_P1; auto with real. }
        symmetry in H22. rewrite (Mult_P4 1), Mult_P1, (Mult_P4 b) in H22;
        auto with real. }
      rewrite H21, H22. rewrite PlusMult_Co3, Mult_P3, <-Mult_P5, 
      <-PlusMult_Co3; auto with real. symmetry. rewrite PlusMult_Co3, Mult_P3,
      <-PlusMult_Co3, Minus_P3, Minus_P4, Plus_P4; auto with real. }
    rewrite (Mult_P4 1), Mult_P1, (Mult_P4 1), Mult_P1 in H21; auto with real. 
    rewrite H21. assert (｜((y[n] - b) / (y[n] · b))｜ = 
      ｜(-((y[n] - b) / (y[n] · b)))｜). { apply Abs_P2; auto with real. }
    rewrite <-H22. assert (y[n] · b ≠ 0).
    { intro. elim Hj; apply (RMult_eq' _ _ b); auto with real.
      rewrite (Mult_P4 0), PlusMult_Co1; auto with real. }
    assert (｜(y[n] · b)｜ = ｜(y[n])｜ · ｜b｜). { apply Abs_P3; auto. }
    rewrite Abs_div, H24; auto with real.
    assert (0 < ｜(y[n])｜ · ｜b｜).
    { apply OrderPM_Co5; auto with real. left; split.
      split; [apply Abs_P1; auto|intro; elim Hj; apply Abs_P1; auto].
      split; [apply Abs_P1; auto|intro; elim H2; apply Abs_P1; auto]. }
    assert (｜(y [n])｜ · ｜b｜ ∈ ℝ). { auto with real. }
    assert (｜(y [n])｜ · ｜b｜ ∈ (ℝ ~ [0])). 
    { apply MKT4'; split; auto. apply AxiomII; split; eauto.
      intro. apply MKT41 in H27; eauto with real.
      rewrite H27 in H25. destruct H25; auto. }
    assert (0 < (｜(y[n])｜ · ｜b｜)⁻). { apply OrderPM_Co10; auto with real. }
    apply Mult_inv1 in H27 as Ho; apply MKT4' in Ho as [Ho _].
    apply (OrderPM_Co7a _ _ (｜(y[n])｜ · ｜b｜)⁻) in H15 as Hn; auto with real.
    apply (Rlt_trans _ (ε · ((｜(y[n])｜ · ｜b｜)⁻)) _); auto with real.
    (* Note: 传递右侧证明 *)
    assert (｜b｜ / (1 + 1) ∈ ℝ /\ ｜(y[n])｜ ∈ ℝ) as [].
    { split; auto with real. }
    assert (0 < ｜b｜ / (1 + 1)).
    { apply OrderPM_Co5; auto with real. left; split; auto.
      split; [apply Abs_P1; auto|intro; elim H2; apply Abs_P1; auto]. }
    pose proof (OrderPM_Co11 _ _ H29 H30 H31 H16) as [].
    apply Rinv_add_cond in Hy as Hl, H18 as Hk.
    apply Mult_inv1 in Hl as HA; apply MKT4' in HA as [HA _].
    apply Mult_inv1 in Hk as HB; apply MKT4' in HB as [HB _].
    rewrite Rinv_mult_distr, Mult_P3, (Mult_P4 ε), <-Mult_P3; auto with real.
    rewrite <-(Mult_P3 (1 + 1)), (Mult_P4 ε ((b · b)⁻)), (Mult_P3 (1 + 1));
    auto with real. assert (b · b = ｜b｜ · ｜b｜).
    { destruct (Leq_P4 b 0); auto with real.
      - assert (｜b｜ = - b). { apply le_zero_Abs; auto. }
        rewrite H35. rewrite PlusMult_Co3, Mult_P3, (Mult_P4 (((-(1)) · b))),
        <-PlusMult_Co3, <-PlusMult_Co3, Minus_P4; auto with real.
      - assert (｜b｜ = b). { apply me_zero_Abs; auto. }
        rewrite H35; auto. }
    rewrite H34, Rinv_mult_distr; auto. rewrite <-(Mult_P3 (1 + 1)),
    <-(Mult_P3 (｜b｜⁻)), (Mult_P4 (｜b｜⁻) ε), (Mult_P3 (1 + 1)); auto with real.
    assert (0 < ε · ((｜b｜)⁻)).
    { apply OrderPM_Co5; auto. left; split; auto.
      apply OrderPM_Co10; auto with real.
      split; [apply Abs_P1; auto|intro; elim H2; apply Abs_P1; auto]. }
    apply (OrderPM_Co7a _ _ (ε · ((｜b｜)⁻))); auto with real.
    assert ((1 + 1) · ((｜b｜)⁻) = (｜ b ｜ / (1 + 1))⁻).
    { rewrite Rinv_mult_distr; auto with real.
      assert ((｜b｜)⁻ / (1 + 1)⁻ = ((｜b｜)⁻ · (1 + 1)) / ((1 + 1)⁻ · (1 + 1))).
      { apply Mult_inv1 in Hf as HC. apply Frac_P1; auto. }
      rewrite (Mult_P4 ((1 + 1)⁻)), Divide_P1, Divide_P2 in H36; auto with real.
      rewrite H36. rewrite Mult_P4; auto with real. }
    (* ****** rewrite <-H36 in H33. ****** *)
    assert ((｜(y[n])｜) ⁻ < (｜b｜ / (1 + 1))⁻); auto. 
    rewrite <-H36 in H37. auto. }
  assert (IsSeq \{\ λ n v, n ∈ ℕ /\ v ∈ ℝ /\ v = (y[n])⁻ \}\).
  { destruct H as [H []]. repeat split; intros.
    - unfold Relation; intros. apply AxiomII in H10 as [_[x0 [y0]]];
      exists x0, y0; tauto.
    - apply AxiomII' in H10 as [_[H10 []]];
      apply AxiomII' in H11 as [_[_[H11]]]. rewrite H14; auto.
    - apply AxiomI; split; intros.
      + apply AxiomII in H10 as [H10 []]. apply AxiomII' in H11; tauto.
      + assert (y[z] ∈ ℝ).
        { apply H9, (@ Property_ran z), Property_Value; auto; 
          rewrite H8; auto. }
        assert (y[z] ∈ (ℝ ~ [0])).
        { apply H1 in H10 as Hj. apply MKT4'; split; auto.
          apply AxiomII; split; eauto. intro.
          apply MKT41 in H12; eauto with real. }
        apply Mult_inv1 in H12 as Hk; apply MKT4' in Hk as [Hk _].
        apply AxiomII; split; eauto. exists (y[z]⁻).
        apply AxiomII'; repeat split; auto. apply MKT49a; eauto.
    - unfold Included; intros. apply AxiomII in H10 as [_[x0]].
      apply AxiomII' in H10; tauto. }
  split; auto; intros. pose proof H9; destruct H10 as [].
  assert ((1 + 1)⁻ · ε · (b · b) ∈ ℝ /\ 0 < (1 + 1)⁻ · ε · (b · b)).
  { split; auto with real.
    apply (OrderPM_Co7a _ _ (1 + 1)⁻) in H11; auto with real.
    rewrite Mult_P4, PlusMult_Co1, Mult_P4 in H11; auto with real.
    apply (OrderPM_Co7a _ _ (b · b)) in H11; auto with real.
    rewrite Mult_P4, PlusMult_Co1 in H11; auto with real. }
  apply H7 in H12. destruct H12 as [N []]. exists N; split; auto; intros.
  apply H13 in H15; auto. rewrite <-Mult_P3, <-Mult_P3, Divide_P1, Mult_P1,
  Mult_P3, Divide_P1, Mult_P4, Mult_P1 in H15; auto with real.
  assert ((y[n])⁻ = \{\ λ n v, n ∈ ℕ /\ v ∈ ℝ /\ v = (y[n])⁻ \}\ [n]).
  { destruct H as [H []], H8 as [H8 _].
    assert (y[n] ∈ ℝ).
    { apply H17, (@ Property_ran n), Property_Value; auto; rewrite H16; auto. }
    assert (y[n] ∈ (ℝ ~ [0])).
    { apply H1 in H14 as HD. apply MKT4'; split; auto.
      apply AxiomII; split; eauto. intro.
      apply MKT41 in H19; eauto with real. }
    apply Mult_inv1 in H19 as HE; apply MKT4' in HE as [HE _].
    apply Property_Fun; auto. apply AxiomII'; repeat split; auto. 
    apply MKT49a; eauto. }
  rewrite <-H16; auto.
Qed.

(* x y是收敛数列,y(n), lim y 均不为0, lim(x/y) = limx/limy *)
Theorem Theorem2_7_4 : ∀ x y, IsSeq x -> IsSeq y
  -> Convergence x -> Convergence y
  -> (∀ n, n ∈ ℕ -> y[n] ≠ 0)-> lim y ≠ 0
  -> Convergence \{\ λ n v, n ∈ ℕ /\ v ∈ ℝ /\ v = x[n] / y[n] \}\
    /\ lim \{\ λ n v, n ∈ ℕ /\ v ∈ ℝ /\ v = x[n] / y[n] \}\ = lim x / lim y.
Proof.
  intros. pose proof H1; pose proof H2.
  destruct H5 as [a [Ha Hb]], H6 as [b [Hc Hd]].
  apply Lim_getValue in Hb as He; auto; apply Lim_getValue in Hd as Hf; auto.
  pose proof H as Hg; pose proof H0 as Hh.
  destruct Hg as [Hg []], Hh as [Hh []].
  set (y' := \{\ λ n v, n ∈ ℕ /\ v ∈ ℝ /\ v = (y[n])⁻ \}\).
  assert (IsSeq y').
  { repeat split; intros.
    - unfold Relation; intros. apply AxiomII in H9 as [_[x0 [y0]]].
      exists x0, y0; tauto.
    - apply AxiomII' in H9 as [_[H9 []]];
      apply AxiomII' in H10 as [_[_ []]]. rewrite H13; auto.
    - apply AxiomI; split; intros.
      + apply AxiomII in H9 as [_[y0]]. apply AxiomII' in H9; tauto.
      + apply H3 in H9 as Hi. assert (y[z] ∈ ℝ).
        { apply H8, (@ Property_ran z), Property_Value; auto;
          rewrite H7; auto. }
        assert (y[z] ∈ (ℝ ~ [0])).
        { apply MKT4'; split; auto. apply AxiomII; split; eauto.
          intro. apply MKT41 in H11; eauto with real. }
        apply Mult_inv1 in H11 as Hj; apply MKT4' in Hj as [Hj _].
        apply AxiomII; split; eauto. exists ((y[z])⁻).
        apply AxiomII'; repeat split; auto. apply MKT49a; eauto.
    - unfold Included; intros. apply AxiomII in H9 as [_[x0]].
      apply AxiomII' in H9; tauto. }
  assert (Limit_Seq y' (b)⁻).
  { rewrite <-Hf. apply Theorem2_7_4'; auto. }
  pose proof H9 as Hj; destruct H9 as [H9 _].
  assert (∀n, n ∈ ℕ -> (y[n])⁻ = y'[n]).
  { intros. apply H3 in H11 as Hk.
    assert (y[n] ∈ ℝ).
    { apply H8, (@ Property_ran n), Property_Value; auto;
      rewrite H7; auto. }
    assert (y[n] ∈ (ℝ ~ [0])).
    { apply MKT4'; split; auto. apply AxiomII; split; eauto.
      intro. apply MKT41 in H13; eauto with real. }
    apply Mult_inv1 in H13 as Hl; apply MKT4' in Hl as [Hl _].
    apply Property_Fun; auto. apply AxiomII'; repeat split; auto.
    apply MKT49a; eauto. }
  assert (\{\ λ n v, n ∈ ℕ /\ v ∈ ℝ /\ v = x[n] / y[n] \}\
    = \{\ λ n v, n ∈ ℕ /\ v ∈ ℝ /\ v = x[n] · y'[n] \}\).
  { apply AxiomI; split; intros.
    - apply AxiomII in H12 as [H12 [x0 [y0 [H13 [H14 []]]]]].
      apply AxiomII; split; auto. exists x0, y0; repeat split; auto.
      apply H11 in H14. rewrite <-H14; auto.
    - apply AxiomII in H12 as [H12 [x0 [y0 [H13 [H14 []]]]]].
      apply AxiomII; split; auto. exists x0, y0; repeat split; auto.
      apply H11 in H14; rewrite H14; auto. }
  assert (b ∈ (ℝ ~ [0])).
  { rewrite Hf in H4. apply MKT4'; split; auto. apply AxiomII; split; eauto.
    intro. apply MKT41 in H13; eauto with real. }
  apply Mult_inv1 in H13 as Hk; apply MKT4' in Hk as [Hk _].
  assert (lim y' = (lim y)⁻).
  { apply Lim_getValue in H10; auto. rewrite Hf; auto. }
  assert (Convergence y').
  { exists (b)⁻; split; auto. }
  rewrite H12, <-H14. apply Theorem2_7_3; auto.
Qed.

(* k ≤ nk *)
Fact fn_ge_n : ∀ f n, Function f -> dom(f) = ℕ -> ran(f) ⊂ ℕ
  -> n ∈ dom(f) -> StrictIncreaseFun f -> n ≤ f[n].
Proof.
  intros. set (F:= \{ λ n, n ∈ ℕ /\ n ≤ f[n] \}).
  assert (F = ℕ).
  { apply MathInd_Ma; unfold Included; intros.
    - apply AxiomII in H4; tauto.
    - apply AxiomII; repeat split; eauto with real.
      assert (f[1] ∈ ℕ). 
      { apply H1, (@ Property_ran 1), Property_Value; auto; 
        rewrite H0; auto with real. }
      pose proof one_is_min_in_N. apply H5; auto.
    - apply AxiomII in H4 as [H4 []].
      assert (x ∈ dom(f) /\ (x + 1) ∈ dom(f)) as [].
      { split; [rewrite H0; auto|rewrite H0; auto with real]. }
      assert (f[x] ∈ ℕ /\ f[x + 1] ∈ ℕ) as [].
      { split; [apply H1, (@ Property_ran x), Property_Value; auto
        |apply H1, (@ Property_ran (x + 1)), Property_Value; auto]. }
      apply AxiomII; repeat split; eauto with real.
      assert (f[x] < f[x + 1]).
      { apply H3; auto. apply Nat_P4a; auto with real.
        apply Leq_P1; auto with real. }
      apply Nat_P4; auto. apply (Order_Co2 _ f[x] _); auto with real. }
  rewrite H0, <-H4 in H2. apply AxiomII in H2; tauto.
Qed.

(* 定义1 子列(y 是 x 的子列) *)
Definition SubSeq x y := IsSeq x /\ IsSeq y
  /\ (∃ f, StrictIncreaseFun f /\ dom(f) = ℕ /\ ran(f) ⊂ ℕ
    /\ (∀ n, n ∈ ℕ -> y[n] = x[f[n]])).

(* 定理2.8 数列收敛的充要条件 *)
Theorem Theorem2_8 : ∀ x, IsSeq x -> (Convergence x 
  <-> (∀ y, SubSeq x y -> Convergence y)).
Proof.
  split; intros.
  - destruct H0 as [a [Ha [_]]]. destruct H1 as [Hb [Hc [f [Hd [He [Hf]]]]]].
    exists a; split; auto. split; auto; intros.
    apply H0 in H2 as [N [H2]]. exists N; split; auto; intros.
    apply H1 in H4 as H6. rewrite H6. pose proof Hd; destruct Hd.
    assert (n ≤ f[n]).
    { rewrite <-He in H4. apply fn_ge_n; auto. }
    assert (f[n] ∈ ℕ).
    { apply Hf, (@ Property_ran n), Property_Value; auto; rewrite He; auto. }
    assert (N < f[n]). { apply (Order_Co2 _ n _); auto with real. }
    apply H3 in H12; auto.
  - assert (SubSeq x x).
    { unfold SubSeq; split; auto; split; auto.
      exists \{\ λ u v, u ∈ ℕ /\ v ∈ ℕ /\ v = u \}\.
      assert (Function \{\ λ u v, u ∈ ℕ /\ v ∈ ℕ /\ v = u \}\).
      { split; intros.
        --- unfold Relation; intros. apply AxiomII in H1 as [_[x0 [y0]]].
           exists x0, y0; tauto.
        --- apply AxiomII' in H1 as [_[H1 []]], H2 as [_[_[H5]]].
           rewrite H2; auto. }
      assert (StrictIncreaseFun \{\ λ u v, u ∈ ℕ /\ v ∈ ℕ /\ v = u \}\).
      { split; auto; intros.
        apply AxiomII in H2 as [_[y1]], H3 as [_[y2]].
        apply AxiomII' in H2 as [Ha [Hb []]], H3 as [Hc [Hd []]].
        assert (y1 = \{\ λ u v, u ∈ ℕ /\ v ∈ ℕ /\ v = u \}\ [x1]).
        { apply Property_Fun; auto. apply AxiomII'; repeat split; auto. }
        assert (y2 = \{\ λ u v, u ∈ ℕ /\ v ∈ ℕ /\ v = u \}\ [x2]).
        { apply Property_Fun; auto; apply AxiomII'; repeat split; auto. }
        rewrite <-H7, <-H8. rewrite H5, H6; auto. }
      split; auto. repeat split.
      -- apply AxiomI; split; intros.
         ++ apply AxiomII in H3 as [_[y0]]. apply AxiomII' in H3; tauto.
         ++ apply AxiomII; split; eauto. exists z.
            apply AxiomII'; repeat split; auto. apply MKT49a; eauto.
      -- unfold Included; intros. apply AxiomII in H3 as[_[x0]].
         apply AxiomII' in H3; tauto.
      -- intros. assert (n = \{\ λ u v, u ∈ ℕ /\ v ∈ ℕ /\ v = u \}\ [n]).
         { apply Property_Fun; auto. apply AxiomII'; repeat split; eauto.
           apply MKT49a; eauto. }
         rewrite <-H4; auto. }
    apply H0 in H1; auto.
Qed.

(* 收敛数列的任意子列具有相同极限 *)
Corollary Lim_SubSeq : ∀ x a, a ∈ ℝ -> Limit_Seq x a ->
  (∀ y, SubSeq x y -> Limit_Seq y a).
Proof.
  intros. destruct H0 as [Ha Hb]. unfold SubSeq in H1.
  destruct H1 as [H1 [H2 [f [H3 [H4 []]]]]]. split; auto; intros.
  apply Hb in H6 as [N [H6]]. exists N; split; auto; intros.
  pose proof H3; destruct H3. assert (f[n] ∈ ℕ).
  { apply H0, (@ Property_ran n), Property_Value; auto; rewrite H4; auto. }
  apply H5 in H8 as Hc. rewrite Hc. apply H7; auto.
  apply (Order_Co2 _ n _); auto with real. rewrite <-H4 in H8.
  left; split; auto. apply fn_ge_n; auto.
Qed.

(* 2.3 数列极限存在的条件 *)

(* 定义：单调递增数列 *)
Definition MonoIncreaseSeq x := IsSeq x /\ (∀ n, n ∈ ℕ -> x[n] ≤ x[n + 1]).

(* 定义：单调递减数列 *)
Definition MonoDecreaseSeq x := IsSeq x /\ (∀ n, n ∈ ℕ -> x[n + 1] ≤ x[n]).

(* 定义：单调数列 *)
Definition MonotonicSeq x := MonoIncreaseSeq x \/ MonoDecreaseSeq x.

(* 定义：有界数列 *)
Definition BoundedSeq x:= IsSeq x /\ 
  (∃ M, M ∈ ℝ /\ ∀ n, n ∈ ℕ -> ｜(x[n])｜ ≤ M).

(* 定理：单调数列的等价性 *)
Theorem MonoIncreaseSeq_Equal : ∀ x, MonoIncreaseSeq x 
  <-> (IsSeq x /\ (∀ n1 n2, n1 ∈ ℕ -> n2 ∈ ℕ -> n1 < n2 -> x[n1] ≤ x[n2])).
Proof.
  split; intros. 
  - destruct H. split; auto. intros. destruct H as [Ha [Hb Hc]].
    set (F:= \{ λ n2, n2 ∈ ℕ /\ (∀ n1, n1 ∈ ℕ -> n1 < n2 -> x[n1] ≤ x[n2])\}).
    assert (F = ℕ).
    { apply MathInd_Ma; unfold Included; intros.
      -- apply AxiomII in H; tauto.
      -- apply AxiomII; repeat split; eauto with real.
         intros. pose proof H. apply one_is_min_in_N in H. destruct H4.
         elim H6. apply Leq_P2; auto with real.
      -- apply AxiomII in H as [H [H4]].
         apply AxiomII; repeat split; eauto with real.
         intros. assert (x[n0] ∈ ℝ /\ x[x0] ∈ ℝ ) as [Hd He].
         { split; [apply Hc, (@ Property_ran n0), Property_Value; auto;
           rewrite Hb; auto|apply Hc, (@ Property_ran x0), Property_Value;
           auto; rewrite Hb; auto]. }
         assert (x[x0 + 1] ∈ ℝ) as Hf.
         { apply Hc, (@ Property_ran (x0 + 1)), Property_Value; auto;
           rewrite Hb; auto with real. }
         destruct (Order_Co1 n0 x0) as [H8 | [|]]; auto with real.
         ++ apply H0 in H4 as H9. apply (Leq_P3 _ x[x0] _); auto.
         ++ apply Nat_P4 in H8; auto. apply Nat_le_ngt in H8; auto with real.
            contradiction.
         ++ rewrite H8. apply H0; auto. }
    rewrite <-H in H2. apply AxiomII in H2 as [H2 []]. apply H5; auto.
  - destruct H. split; auto. intros. pose proof OrderPM_Co9.
    assert (n < n + 1).
    { assert (n + 0 < n + 1).
      { apply OrderPM_Co4; auto with real. apply Leq_P1; auto with real. }
      rewrite Plus_P1 in H3; auto with real. }
    apply H0; auto with real.
Qed.

Theorem MonoDecreaseSeq_Equal : ∀ x, MonoDecreaseSeq x
  <-> (IsSeq x /\ (∀ n1 n2, n1 ∈ ℕ -> n2 ∈ ℕ -> n1 < n2 -> x[n2] ≤ x[n1])).
Proof.
  split; intros.
  - destruct H; split; auto; intros. destruct H as [Ha [Hb Hc]].
    set (F:= \{ λ n2, n2 ∈ ℕ /\ (∀ n1, n1 ∈ ℕ -> n1 < n2 -> x[n2] ≤ x[n1]) \}).
    assert (F = ℕ).
    { apply MathInd_Ma; unfold Included; intros.
      -- apply AxiomII in H; tauto.
      -- apply AxiomII; repeat split; eauto with real. intros.
         apply one_is_min_in_N in H as H5. destruct H4. elim H6.
         apply Leq_P2; auto with real.
      -- apply AxiomII in H as [H []].
         apply AxiomII; repeat split; eauto with real. intros.
         assert (x[n0] ∈ ℝ /\ x[x0] ∈ ℝ) as [].
         { split; [apply Hc, (@ Property_ran n0), Property_Value; auto;
           rewrite Hb; auto| apply Hc, (@ Property_ran x0), Property_Value;
           auto; rewrite Hb; auto]. }
         assert (x[x0 + 1] ∈ ℝ).
         { apply Hc, (@ Property_ran (x0 + 1)), Property_Value; auto;
           rewrite Hb; auto with real. }
         destruct (Order_Co1 n0 x0) as [H11 | [|]]; auto with real.
         ++ apply H0 in H4 as H12. apply (Leq_P3 _ x[x0] _); auto.
         ++ apply Nat_P4 in H11; auto. apply Nat_le_ngt in H11; auto with real.
            contradiction.
         ++ rewrite H11; apply H0; auto. }
    rewrite <-H in H2. apply AxiomII in H2 as [_[]]. apply H4; auto.
  - destruct H; split; auto. intros.
    assert (n < n + 1).
    { assert (n + 0 < n + 1).
      { apply OrderPM_Co4; auto with real. apply Leq_P1; auto with real. }
      rewrite Plus_P1 in H2; auto with real. }
    apply H0; auto with real.
Qed.

Corollary OrderPM_Co1a : ∀ x y z, x ∈ ℝ -> y ∈ ℝ -> z ∈ ℝ
  -> x + z < y + z -> x < y.
Proof.
  intros. apply (OrderPM_Co1 _ _ (-(z))) in H2; auto with real.
  rewrite <-Plus_P3, <-Plus_P3, Minus_P1, Plus_P1, Plus_P1 in H2;
  auto with real.
Qed.

Corollary Plus_Leq_Cancel : ∀ x y z, x ∈ ℝ -> y ∈ ℝ -> z ∈ ℝ
  -> x + z ≤ y + z -> x ≤ y.
Proof.
  intros. apply (Plus_Leq _ _ (- z)) in H2; auto with real.
  rewrite <-Plus_P3, <-Plus_P3, Minus_P1, Plus_P1, Plus_P1 in H2;
  auto with real.
Qed.

(* 2.9 单调有界定理 *)
Theorem Theorem2_9 : ∀ x, MonotonicSeq x -> BoundedSeq x -> Convergence x.
Proof.
  intros. destruct H0 as [Ha [M [Hb]]]. pose proof Ha as Hc.
  destruct Hc as [Hc [Hd He]]. assert (ran(x) ≠ Φ).
  { apply NEexE. exists x[1]. apply Property_dm; auto.
    rewrite Hd; auto with real. }
  pose proof Sup_Inf_Principle _ He H1 as [Hf Hg].
  destruct H as [|].
  - assert ((∃ M, UpperBound ran(x) M)).
    { exists M. unfold UpperBound; repeat split; auto. intros xn H2.
      apply AxiomII in H2 as [H2 [n]]. apply Property_Fun in H3 as H4; auto.
      apply Property_dom in H3 as H5; rewrite Hd in H5. rewrite H4.
      assert (x[n] ∈ ℝ).
      { apply He, (@ Property_ran n), Property_Value; auto; rewrite Hd; auto. }
      assert (0 ≤ M). 
      { apply (Leq_P3 _ ｜(x[n])｜ _); auto with real; apply Abs_P1; auto. }
      apply H0 in H5 as H8. apply Abs_P4 in H8 as []; auto. }
    apply Hf in H2 as H3. destruct H3 as [a [H3]]. destruct H3, H3 as [_[]]. 
    exists a; split; auto. split; auto; intros.
    pose proof H7; destruct H8. pose proof H9; destruct H10 as [Hz Hy].
    assert (a - ε ∈ ℝ). { auto with real. }
    assert (a - ε < a).
    { apply OrderPM_Co2a in H9; auto. apply (OrderPM_Co1 _ _ a) in H9;
      auto with real. rewrite (Plus_P4 0), Plus_P1, Plus_P4 in H9;
      auto with real. }
    pose proof (H5 _ H10 H11) as [xN []]. pose proof H12.
    apply AxiomII in H12 as [_ [N]]. apply Property_Fun in H12 as H15; auto.
    apply Property_dom in H12 as H16; rewrite Hd in H16.
    rewrite H15 in H13, H14. exists N; split; auto; intros.
    assert (x[n] ∈ ℝ).
    { apply He, (@ Property_ran n), Property_Value; auto; rewrite Hd; auto. }
    assert (x[n] ≤ a).
    { rewrite <-Hd in H17. apply Property_dm in H17; auto. }
    assert (a - ε < x[n]).
    { apply MonoIncreaseSeq_Equal in H as []. apply H21 in H18; auto.
      apply (Order_Co2 _ x[N] _); auto with real. }
    assert (x[n] < a + ε).
    { assert (a < a + ε).
      { apply (OrderPM_Co1 _ _ a) in H9; auto with real.
        rewrite Plus_P4, Plus_P1, Plus_P4 in H9; auto with real. } 
      apply (Order_Co2 _ a _); auto with real. }
    destruct H21, H22. split.
    + apply Abs_P4; auto with real. split.
      * apply (Plus_Leq_Cancel _ _ a); auto with real. 
        rewrite <-Plus_P3, (Plus_P4 (- a)), Minus_P1, Plus_P1, Plus_P4;
        auto with real.
      * apply (Plus_Leq_Cancel _ _ a); auto with real.
        rewrite <-Plus_P3, (Plus_P4 (- a)), Minus_P1, Plus_P1, Plus_P4;
        auto with real.
    + intro. assert (x[n] - a ≤ 0).
      { apply (Plus_Leq _ _ (- a)) in H20; auto with real.
        rewrite Minus_P1 in H20; auto. }
      assert (｜(x[n] - a)｜ = - (x[n] - a)). 
      { apply le_zero_Abs; auto with real. }
      rewrite Minus_P3, Minus_P4 in H27; auto with real. rewrite H27 in H25.
      apply (RPlus_eq _ _ (- a)) in H25; auto with real.
      rewrite <-Plus_P3, Minus_P1, Plus_P1, Plus_P4 in H25; auto with real.
      apply (RMult_eq _ _ (-(1))) in H25; auto with real.
      rewrite Mult_P4, PlusMult_Co4, Mult_P4, <-PlusMult_Co3,
      Minus_P3, Minus_P4 in H25; auto with real.
  - assert (∃ L, LowerBound ran(x) L).
    { exists (- M). unfold LowerBound; repeat split; auto with real.
      intros xn H2. apply AxiomII in H2 as [_[n]].
      apply Property_Fun in H2 as H3; auto.
      apply Property_dom in H2 as H4; rewrite Hd in H4. rewrite H3.
      assert (x[n] ∈ ℝ).
      { apply He, (@ Property_ran n), Property_Value; auto; rewrite Hd; auto. }
      assert (0 ≤ M).
      { apply (Leq_P3 _ ｜(x[n])｜ _); auto with real. apply Abs_P1; auto. }
      apply H0 in H4. apply Abs_P4 in H4 as [H4 _]; auto. }
    apply Hg in H2 as [a []]. destruct H2, H2 as [_[]]. exists a; split; auto.
    split; auto; intros. destruct H6; pose proof H7; destruct H8.
    assert (a < a + ε).
    { apply (OrderPM_Co1 _ _ a) in H7; auto with real.
      rewrite Plus_P4, Plus_P1, Plus_P4 in H7; auto with real. }
    apply H4 in H10 as [xN []]; auto with real.
    apply AxiomII in H10 as H12. destruct H12 as [_[N]].
    apply Property_Fun in H12 as H13; auto.
    apply Property_dom in H12 as H14; rewrite Hd in H14.
    rewrite H13 in H10, H11. exists N; split; auto; intros.
    assert (x[n] ∈ ℝ).
    { apply He, (@ Property_ran n), Property_Value; auto; rewrite Hd; auto. }
    assert (x[n] < a + ε).
    { apply MonoDecreaseSeq_Equal in H as []. apply H18 in H16; auto.
      apply (Order_Co2 _ (x[N]) _); auto with real. }
    assert (a ≤ x[n]).
    { rewrite <-Hd in H15. apply Property_dm in H15; auto. }
    assert (a - ε < x[n]).
    { assert (a - ε < a).
      { apply OrderPM_Co2a in H7; auto.
        apply (OrderPM_Co1 _ _ a) in H7; auto with real.
        rewrite Plus_P4, (Plus_P4 0), Plus_P1 in H7; auto with real. }
      apply (Order_Co2 _ a _); auto with real. }
    destruct H18, H20. split.
    + apply Abs_P4; auto with real. split.
      * apply (Plus_Leq_Cancel _ _ a); auto with real.
        rewrite <-Plus_P3, (Plus_P4 (- a)), Minus_P1, Plus_P1, Plus_P4;
        auto with real.
      * apply (Plus_Leq_Cancel _ _ a); auto with real.
        rewrite <-Plus_P3, (Plus_P4 (- a)), Minus_P1, Plus_P1, Plus_P4;
        auto with real.
    + intro. assert (｜(x[n] - a)｜ = (x[n] - a)).
      { apply (Plus_Leq _ _ (- a)) in H19; auto with real.
        rewrite Minus_P1 in H19; auto. apply me_zero_Abs; auto with real. }
      rewrite H24 in H23. apply (RPlus_eq _ _ a) in H23; auto with real.
      rewrite <-Plus_P3, (Plus_P4 (- a)), Minus_P1, Plus_P1, Plus_P4 in H23;
      auto with real.
Qed.

(* 2.10 致密性定理：任何有界数列必定有收敛的子列 *)
Theorem Theorem2_10 : ∀ x, BoundedSeq x -> (∃ y, SubSeq x y /\ Convergence y).
Proof.
  Admitted.

(* 2.11 柯西收敛准则 *)
Theorem Theorem2_11 : ∀ x, IsSeq x -> Convergence x 
  <-> (∀ ε, ε ∈ ℝ /\ 0 < ε -> (∃ N, N ∈ ℕ /\ ∀ n m, n ∈ ℕ -> m ∈ ℕ 
    -> N < n -> N < m -> ｜(x[n] - x[m])｜ < ε)).
Proof.
  assert ((1 + 1) ∈ ℝ) as Ha. { auto with real. }
  assert (0 < 1 + 1) as Hb.
  { assert (0 + 0 < 1 + 1).
    { apply OrderPM_Co4; auto with real. apply OrderPM_Co9. }
    rewrite Plus_P1 in H; auto with real. }
  assert (0 < (1 + 1)⁻) as Hc. { apply OrderPM_Co10; auto. }
  assert ((1 + 1) ∈ (ℝ ~ [0])) as Hd.
  { apply MKT4'; split; auto with real. apply AxiomII; split; eauto.
    intro. apply MKT41 in H; eauto with real. rewrite H in Hb.
    destruct Hb; auto. }
  apply Mult_inv1 in Hd as He; apply MKT4' in He as [Hf _].
  split; intros.
  - destruct H0 as [A [Hg [_]]]. pose proof H1 as Hh. destruct H1 as [Hi Hj].
    assert (ε / (1 + 1) ∈ ℝ /\ 0 < ε / (1 + 1)).
    { split; auto with real. apply OrderPM_Co5; auto. }
    apply H0 in H1 as H2; destruct H2 as [N1 []].
    apply H0 in H1 as H4; destruct H4 as [N2 []].
    destruct (Max_nat_2 _ _ H2 H4) as [N [H6 []]].
    exists N; split; auto; intros.
    assert (N1 < n /\ N2 < m) as [].
    { split; [apply (Ntrans _ N _); auto|apply (Ntrans _ N _); auto]. }
    apply H3 in H13; auto; apply H5 in H14; auto.
    assert (x[n] ∈ ℝ /\ x[m] ∈ ℝ) as [Hk Hl].
    { destruct H as [H []]. split; [apply H16, (@ Property_ran n),
      Property_Value; auto; rewrite H15; auto| apply H16, (@ Property_ran m),
      Property_Value; auto; rewrite H15; auto]. }
    assert (｜(A - x[m])｜ = ｜(x[m] - A)｜). { apply Abs_P7; auto. }
    apply (Order_Co2 _ (｜(x[n] - A)｜+ ｜(A - x[m])｜) _); auto with real.
    right; split. apply Abs_P8; auto.
    assert (ε + ε = ε · (1 + 1)).
    { rewrite Mult_P4, Mult_P5, (Mult_P4 1), Mult_P1; auto with real. }
    assert (ε = ((ε + ε) · (1 + 1)⁻)).
    { rewrite H16, <-Mult_P3, Divide_P1, Mult_P1; auto. }
    assert (ε = ε / (1 + 1) + ε / (1 + 1)). { rewrite <-Mult_P5; auto. }
    rewrite H18, H15. destruct H13. apply OrderPM_Co4; auto with real.
  - assert (BoundedSeq x).
    { unfold BoundedSeq; split; auto.
      assert (1 ∈ ℝ /\ 0 < 1). { split; auto with real. apply OrderPM_Co9. }
      apply H0 in H1 as [N0 []]. assert (N0 < N0 + 1).
      { apply Nat_P4a; auto with real. apply Leq_P1; auto with real. }
      assert (∀ n, n ∈ ℕ -> N0 < n -> ｜(x[n] - x[N0 + 1])｜ < 1).
      { intros. apply H2; auto with real. }
      assert (x[N0 + 1] ∈ ℝ) as Hz.
      { destruct H as [H []]; apply H6, (@ Property_ran (N0 + 1)),
        Property_Value; auto; rewrite H5; auto with real. }
      assert (∀ n, n ∈ ℕ -> N0 < n -> ｜(x[n])｜ ≤ ｜(x[N0 + 1])｜ + 1).
      { intros. apply H4 in H6 as H7; auto.
        assert (x[n] ∈ ℝ).
        { destruct H as [H []]; apply H9, (@ Property_ran n), Property_Value;
          auto; rewrite H8; auto. }
        assert (｜(x[n])｜ = ｜(x[N0 + 1] + (x[n] - x[N0 + 1]))｜).
        { rewrite (Plus_P4 x[n]), Plus_P3, Minus_P1, Plus_P4, Plus_P1;
          auto with real. }
        apply (Order_Co2 _ (｜(x[N0 + 1])｜ + ｜(x[n] - x[N0 + 1])｜) _);
        auto with real. right; split.
        --- rewrite H9. apply Abs_P5; auto with real.
        --- apply OrderPM_Co4; auto with real. apply Leq_P1; auto with real. }
      set (F:= \{ λ N0, N0 ∈ ℕ
        /\ (∃ M1, M1 ∈ ℝ /\ ∀ n, n ∈ ℕ -> n ≤ N0 -> ｜(x[n])｜ ≤ M1) \}).
      assert (F = ℕ).
      { apply MathInd_Ma; unfold Included; intros.
        --- apply AxiomII in H6; tauto.
        --- apply AxiomII; repeat split; eauto with real.
            assert (x[1] ∈ ℝ).
            { destruct H as [H []]; apply H7, (@ Property_ran 1),
              Property_Value; auto; rewrite H6; auto with real. }
            exists (｜(x[1])｜); split; auto with real. intros.
            assert (n = 1).
            { apply one_is_min_in_N in H7 as H9. apply Leq_P2; auto with real. }
            rewrite H9. apply Leq_P1; auto with real.
        --- apply AxiomII in H6 as [_[H6 [M0 []]]].
            apply AxiomII; repeat split; eauto with real.
            assert (x[x0 + 1] ∈ ℝ).
            { destruct H as [H []]; apply H10, (@ Property_ran (x0 + 1)),
              Property_Value; auto; rewrite H9; auto with real. }
            destruct (Order_Co1 M0 ｜(x[x0 + 1])｜) as [H10 |[H10 | H10]]; 
            auto with real.
            +++ exists (｜(x[x0 + 1])｜); split; auto with real. intros.
                destruct (classic (n = x0 + 1)).
                *** rewrite H13. apply Leq_P1; auto with real.
                *** assert (n < x0 + 1). { split; auto. }
                    assert (n ≤ x0).
                    { apply Nat_P4 in H14; auto with real.
                      apply (Plus_Leq _ _ (-(1))) in H14; auto with real.
                      rewrite <-Plus_P3, Minus_P1, Plus_P1, <-Plus_P3,
                      Minus_P1, Plus_P1 in H14; auto with real. }
                    assert (x[n] ∈ ℝ).
                    { destruct H as [H []]; apply H17, (@ Property_ran n),
                      Property_Value; auto; rewrite H16; auto. }
                    apply (Order_Co2 _ M0 _); auto with real.
            +++ exists M0; split; auto. intros.
                destruct (classic (n = x0 + 1)).
                *** destruct H10. rewrite H13; auto.
                *** assert (n < x0 + 1). { split; auto. }
                    assert (n ≤ x0).
                    { apply Nat_P4 in H14; auto with real.
                      apply (Plus_Leq _ _ (-(1))) in H14; auto with real.
                      rewrite <-Plus_P3, Minus_P1, Plus_P1, <-Plus_P3,
                      Minus_P1, Plus_P1 in H14; auto with real. }
                    apply H8; auto.
           +++ exists M0; split; auto. intros.
               destruct (classic (n = x0 + 1)).
               *** rewrite H10, H13; apply Leq_P1; auto with real.
               *** assert (n < x0 + 1). { split; auto. }
                   assert (n ≤ x0).
                   { apply Nat_P4 in H14; auto with real;
                     apply (Plus_Leq _ _ (-(1))) in H14; auto with real;
                     rewrite <-Plus_P3, Minus_P1, Plus_P1, <-Plus_P3,
                     Minus_P1, Plus_P1 in H14; auto with real. }
                   apply H8; auto. }
      pose proof H1 as Hy; rewrite <-H6 in Hy.
      apply AxiomII in Hy as [_[_[M []]]].
      destruct (Order_Co1 M (｜(x[N0 + 1])｜ + 1)) as [H9 | [H9 | H9]];
      auto with real.
      -- exists (｜(x[N0 + 1])｜ + 1); split; auto with real. intros.
         assert (x[n] ∈ ℝ).
         { destruct H as [H []]. apply H12, (@ Property_ran n), Property_Value;
           auto; rewrite H11; auto. }
         destruct (Order_Co1 n N0) as [H12 | [H12 | H12]]; auto with real.
         ++ destruct H12. apply H8 in H10 as H14; auto.
            apply (Order_Co2 _ M _); auto with real.
         ++ apply H8 in H10 as H13. apply (Order_Co2 _ M _); auto with real.
            rewrite H12; apply Leq_P1; auto with real.
      -- exists M; split; auto. intros.
         assert (x[n] ∈ ℝ).
         { destruct H as [H []]. apply H12, (@ Property_ran n), Property_Value;
           auto; rewrite H11; auto. }
         destruct (Order_Co1 n N0) as [H12 | [H12 | H12]]; auto with real.
         ++ destruct H12; apply H8; auto.
         ++ apply H5 in H10 as H13; auto.
            apply (Order_Co2 _ (｜(x[N0 + 1])｜ + 1) _); auto with real.
         ++ apply H8; auto. rewrite H12; apply Leq_P1; auto with real.
      -- exists M; split; auto. intros.
         destruct (Order_Co1 n N0) as [H12 | [H12 | H12]]; auto with real.
         ++ destruct H12; auto.
         ++ rewrite H9; auto.
         ++ apply H8; auto. rewrite H12; apply Leq_P1; auto with real. }
    apply Theorem2_10 in H1 as [y [Hz Hy]]. destruct Hy as [ξ [Hy Hx]].
    pose proof Hx as H1. destruct H1. apply Lim_getValue in Hx as Hw; auto.
    destruct Hz as [Hz [_[f [Hu [Ht [Hs]]]]]]. exists ξ; split; auto.
    split; auto; intros. destruct H4 as [].
    assert (ε / (1 + 1) ∈ ℝ /\ 0 < ε / (1 + 1)).
    { split; auto with real. apply OrderPM_Co5; auto. }
    apply H0 in H6 as [N []]. exists N; split; auto; intros.
    assert (∀ k, k ∈ ℕ -> N < k -> ｜(x[n] - y[k])｜ < ε / (1 + 1)).
    { intros. assert (∃ nk, nk ∈ ℕ /\ N < nk /\ y[k] = x[nk]).
      { pose proof H10. rewrite <-Ht in H12.
        pose proof Hu. destruct H13 as [H13 _]. apply fn_ge_n in H12; auto.
        assert (f[k] ∈ ℕ).
        { apply Hs, (@ Property_ran k), Property_Value; auto;
          rewrite Ht; auto. }
        assert (N < f[k]). { apply (Order_Co2 _ k _); auto with real. }
        apply H3 in H10 as H16. exists f[k]; split; auto. }
        destruct H12 as [nk [H12 []]]. rewrite H14; auto. }
    set (z:= \{\ λ k v, k ∈ ℕ /\ v ∈ ℝ /\ v = ｜(x[n] - y[k])｜ \}\).
    assert (x[n] ∈ ℝ) as Hv.
    { destruct Hz as [Hz []]. apply H12, (@ Property_ran n), Property_Value;
      auto; rewrite H11; auto. }
    assert (Function z).
    { split; intros.
      -- unfold Relation; intros. apply AxiomII in H11 as [_[x0 [y0]]].
         exists x0, y0; tauto.
      -- apply AxiomII' in H11 as [H11 [H13 [H14]]].
         apply AxiomII' in H12 as [H12 [H16 [H17]]].
         apply MKT49b in H11 as [], H12 as []. rewrite H15, H18; auto. }
    assert (IsSeq z).
    { split; auto; split.
      -- apply AxiomI; split; intros.
         ++ apply AxiomII in H12 as [_[y0]]. apply AxiomII' in H12; tauto.
         ++ assert (y[z0] ∈ ℝ).
            { destruct H1 as [H1 []]. apply H14, (@ Property_ran z0),
              Property_Value; auto; rewrite H13; auto. }
            assert (｜(x[n] - y[z0])｜ ∈ ℝ). { apply Abs_in_R; auto with real. }
            apply AxiomII; split; eauto. exists ｜(x[n] - y[z0])｜.
            apply AxiomII'; repeat split; auto. apply MKT49a; eauto.
      -- unfold Included; intros. apply AxiomII in H12 as [_[k]].
         apply AxiomII' in H12; tauto. }
    assert (Limit_Seq z ｜(x[n] - ξ)｜).
    { split; auto; intros. destruct Hx as [_ Hx]. apply Hx in H13 as H14.
      destruct H14 as [N0 []], H13. exists N0; split; auto.
      intros. apply H15 in H18 as H19; auto.
      assert (y[n0] ∈ ℝ).
      { destruct H1 as [H1 []]. apply H21, (@ Property_ran n0), 
        Property_Value; auto; rewrite H20; auto. }
      assert (｜(x[n] - y[n0])｜ ∈ ℝ). { auto with real. }
      assert (｜(x[n] - ξ)｜ ∈ ℝ). { auto with real. }
      assert (｜(x[n] - y[n0])｜ = z[n0]).
      { apply Property_Fun; auto. apply AxiomII'; repeat split;
        auto with real. apply MKT49a; eauto. }
      rewrite <-H23. apply (Order_Co2 _ (｜(y[n0] - ξ)｜) _); auto with real.
      right; split; auto.
      assert (y[n0] - ξ = -((x[n] - y[n0]) - (x[n] - ξ))).
      { repeat rewrite Minus_P3, Minus_P4; auto with real. symmetry.
        rewrite (Plus_P4 (x[n])), Plus_P4, <-Plus_P3, (Plus_P3 x[n]),
        Minus_P1, (Plus_P4 0), Plus_P1, Plus_P4; auto with real. }
      assert (｜(x[n] - y[n0] - (x[n] - ξ))｜
        = ｜(-(x[n] - y[n0] - (x[n] - ξ)))｜). { apply Abs_P2; auto with real. }
      rewrite H24, <-H25. apply Abs_P5; auto with real. }
    set (c := \{\ λ n v, n ∈ ℕ /\ v ∈ ℝ /\ v = ε / (1 + 1) \}\).
    assert (Function c).
    { split; intros.
      -- unfold Relation; intros. apply AxiomII in H14 as [_[x0 [y0]]].
         exists x0, y0; tauto.
      -- apply AxiomII' in H14 as [_[H14 []]], H15 as [_[_[]]].
         rewrite H17, H18; auto. }
    assert (IsSeq c).
    { split; auto; split.
      -- apply AxiomI; split; intros.
         ++ apply AxiomII in H15 as [_[y0]]. apply AxiomII' in H15; tauto.
         ++ apply AxiomII; split; eauto. exists (ε / (1 + 1)).
            apply AxiomII'; repeat split; auto with real.
            apply MKT49a; eauto with real.
      -- unfold Included; intros. apply AxiomII in H15 as [_[x0]].
         apply AxiomII' in H15; tauto. }
    assert (Limit_Seq c (ε / (1 + 1))).
    { split; auto. intros. destruct H13 as [_]. apply H13 in H16 as H17.
      destruct H17 as [N0 []], H16. exists N0; split; auto. intros.
      assert (ε / (1 + 1) = c[n0]).
      { apply Property_Fun; auto. apply AxiomII'; repeat split;
        auto with real. apply MKT49a; eauto with real. }
      assert (｜0｜ = 0). { apply Abs_P1; auto with real. }
      assert (｜0｜ < ε0). { rewrite H23; auto. }
      rewrite <-H22, Minus_P1; auto with real. }
    assert (Convergence z /\ Convergence c) as [].
    { split; [exists (｜(x[n] - ξ)｜); split; auto with real|
      exists (ε / (1 + 1)); split; auto with real]. }
    assert (ε / (1 + 1) < ε).
    { assert (1 < (1 + 1)).
      { assert (1 + 0 < 1 + 1).
        { apply OrderPM_Co4; auto with real. apply Leq_P1; auto with real. }
        rewrite Plus_P1 in H19; auto with real. }
      assert (0 < ε / (1 + 1)).
      { apply (OrderPM_Co7a _ _ ((1 + 1)⁻)) in H5; auto with real.
        rewrite Mult_P4, PlusMult_Co1 in H5; auto with real. }
      apply (OrderPM_Co7a _ _ (ε / (1 + 1))) in H19; auto with real.
      rewrite Mult_P4, Mult_P1, (Mult_P4 ε), Mult_P3, Divide_P1,
      (Mult_P4 1), Mult_P1, Mult_P4 in H19; auto with real. }
    apply (Order_Co2 _ (ε / (1 + 1)) _); auto with real. right; split; auto.
    apply Lim_getValue in H13 as H20, H16 as H21; auto with real.
    rewrite <-H20, <-H21. apply Theorem2_5; auto.
    exists N; split; auto. intros. 
    assert (y[n0] ∈ ℝ).
    { destruct H1 as [H1 []]. apply H25, (@ Property_ran n0), Property_Value;
      auto; rewrite H24; auto. }
    assert (｜(x[n] - y[n0])｜ ∈ ℝ). { auto with real. }
    assert (｜(x[n] - y[n0])｜ = z[n0]).
    { apply Property_Fun; auto. apply AxiomII'; repeat split; auto with real.
      apply MKT49a; eauto. }
    assert (ε / (1 + 1) = c[n0]).
    { apply Property_Fun; auto. apply AxiomII'; repeat split; auto with real.
      apply MKT49a; eauto with real. }
    rewrite <-H26, <-H27; apply H10; auto.
Qed.













