section \<open>Sphere2\<close>
theory Sphere2
  imports Smooth_Manifolds.Differentiable_Manifold
begin

(* radius of sphere *)
abbreviation R::real where "R == 2"

typedef (overloaded) ('a::real_normed_vector) sphere =
  "{a::'a\<times>real. norm a = R}"
proof -
  have "norm (0::'a,R::real) = R" by simp
  then show ?thesis by blast
qed

setup_lifting type_definition_sphere

(* First stereographic projection with a rescaling parameter C: between S^n - (0,R) and R^n. *)
lift_definition top_sphere :: "('a::real_normed_vector) sphere" is "(0, R)" by simp

locale rescaling =
  fixes C:: real
  assumes is_non_zero [simp]: "C \<noteq> 0"

lift_definition (in rescaling) st_proj1 :: "('a::real_normed_vector) sphere \<Rightarrow> 'a" is
  "\<lambda>(x,z). (C *\<^sub>R x) /\<^sub>R (R - z)" .

lemma (in rescaling) dumb_computation:
  fixes a
  shows "sqrt
     ((C * (C * (C * (C * 4))) +
       (C * (C * (norm a * (norm a * 8))) + norm a * (norm a * (norm a * (norm a * 4))))) /
      (C * (C * (C * C)) +
       (norm a * (norm a * (norm a * norm a)) + C * (C * (norm a * (norm a * R)))))) =
    R"
proof -
  have "(C * (C * (C * (C * 4))) + (C * (C * (norm a * (norm a * 8))) + norm a * (norm a * (norm a * (norm a * 4))))) 
= 4 * (C * (C * (C * (C))) + (C * (C * (norm a * (norm a * 2))) + norm a * (norm a * (norm a * (norm a)))))" by simp
  moreover have "(C * (C * (C * C)) + (norm a * (norm a * (norm a * norm a)) + C * (C * (norm a * (norm a * R))))) \<noteq> 0"
    using mult_nonneg_nonneg norm_ge_zero by(smt is_non_zero mult.assoc sum_squares_le_zero_iff)
  then have "4 * (C * (C * (C * (C))) + (C * (C * (norm a * (norm a * 2))) + norm a * (norm a * (norm a * (norm a))))) /
                (C * (C * (C * (C))) + (C * (C * (norm a * (norm a * 2))) + norm a * (norm a * (norm a * (norm a))))) = 4"
    by (simp add: divide_eq_imp)
  finally show ?thesis 
    using real_sqrt_four by (simp add: add.commute)
qed

lift_definition (in rescaling) st_proj1_inv :: "('a::real_normed_vector) \<Rightarrow> 'a sphere" is
  "\<lambda>x. ((2 * R * C / ((norm x)\<^sup>2 + C\<^sup>2)) *\<^sub>R x, R * ((norm x)\<^sup>2 - C\<^sup>2) / ((norm x)\<^sup>2 + C\<^sup>2))"
  apply (auto simp: norm_prod_def divide_simps algebra_simps)
  apply (auto simp: power2_eq_square algebra_simps)
  apply (simp add: dumb_computation).

(* Second stereographic projection: between S^n - (0,-R) and R^n. *)
lift_definition bot_sphere :: "('a::real_normed_vector) sphere" is "(0, -R)" by simp

lift_definition (in rescaling) st_proj2 :: "('a::real_normed_vector) sphere \<Rightarrow> 'a" is
  "\<lambda>(x,z). (C *\<^sub>R x) /\<^sub>R (R + z)" .

lift_definition (in rescaling) st_proj2_inv :: "('a::real_normed_vector) \<Rightarrow> 'a sphere" is
  "\<lambda>x. ((2 * R * C / ((norm x)\<^sup>2 + C\<^sup>2)) *\<^sub>R x, R *\<^sub>R (C\<^sup>2 - (norm x)\<^sup>2) / ((norm x)\<^sup>2 + C\<^sup>2))"
  apply (auto simp: norm_prod_def divide_simps algebra_simps)
  apply (auto simp: power2_eq_square algebra_simps)
  apply (simp add: dumb_computation).

instantiation sphere :: (real_normed_vector) topological_space
begin

lift_definition open_sphere :: "'a sphere set \<Rightarrow> bool" is
  "openin (subtopology (euclidean::('a\<times>real) topology) {a. norm a = R})" .

instance
  apply standard
  apply (transfer; auto)
  apply (transfer; auto)
  apply (transfer; auto)
  done

end

instance sphere :: (real_normed_vector) t2_space
  apply standard
  apply transfer
  subgoal for x y
    apply (drule hausdorff[of x y])
    apply clarsimp
    subgoal for U V
      apply (rule exI[where x="U \<inter> {a. norm a = R}"])
      apply clarsimp
      apply (rule conjI) defer
       apply (rule exI[where x="V \<inter> {a. norm a = R}"])
      by auto
    done
  done

instance sphere :: (euclidean_space) second_countable_topology
proof standard
  obtain BB::"('a\<times>real) set set" where BB: "countable BB" "open = generate_topology BB"
    by (metis ex_countable_subbasis)
  let ?B = "(\<lambda>B. B \<inter> {x. norm x = R}) ` BB"
  show "\<exists>B::'a sphere set set. countable B \<and> open = generate_topology B"
    apply transfer
    apply (rule bexI[where x = ?B])
    apply (rule conjI)
    subgoal using BB by force
    subgoal using BB apply clarsimp
      apply (subst openin_subtopology_eq_generate_topology[where BB=BB])
      by (auto )
    subgoal by auto
    done
qed

lemma transfer_continuous_on1[transfer_rule]:
  includes lifting_syntax
  shows "(rel_set (=) ===> ((=) ===> pcr_sphere (=)) ===> (=)) (\<lambda>X::'a::t2_space set. continuous_on X) continuous_on"
  apply (rule continuous_on_transfer_right_total2)
        apply transfer_step
       apply transfer_step
      apply transfer_step
     apply transfer_prover
    apply transfer_step
   apply transfer_step
  apply transfer_prover
  done

lemma transfer_continuous_on2[transfer_rule]:
  includes lifting_syntax
  shows "(rel_set (pcr_sphere (=)) ===> (pcr_sphere (=) ===> (=)) ===> (=)) (\<lambda>X. continuous_on (X \<inter> {x. norm x = R})) (\<lambda>X. continuous_on X)"
  apply (rule continuous_on_transfer_right_total)
        apply transfer_step
       apply transfer_step
      apply transfer_step
     apply transfer_prover
    apply transfer_step
   apply transfer_step
  apply transfer_prover
  done

lemma (in rescaling) st_proj1_inv_continuous:
  "continuous_on UNIV st_proj1_inv"
  by transfer (auto intro!: continuous_intros simp: add_nonneg_eq_0_iff)

lemma (in rescaling) st_proj1_continuous:
  "continuous_on (-{top_sphere}) st_proj1"
  apply transfer 
  apply (auto intro!: continuous_intros simp: add_nonneg_eq_0_iff split_beta' norm_prod_def)
  by (metis add.commute add_cancel_right_right norm_eq_zero power_not_zero real_sqrt_eq_iff real_sqrt_four)

lemma (in rescaling) st_proj1_inv: "st_proj1_inv (st_proj1 x) = x" if "x \<noteq> top_sphere"
  using that
  apply transfer
proof (clarsimp, rule conjI)
  fix a::'a and b::real
  assume *: "norm (a, b) = R" and ab: "a = 0 \<longrightarrow> b \<noteq> R"
  have "b \<noteq> R" 
  proof
    assume asm:"b = R"
    then have "a = 0"
      using * by (metis norm_Pair norm_commute norm_eq_zero power2_abs real_norm_def real_sqrt_sum_squares_eq_cancel)
    thus "False" 
      using ab asm by simp
  qed
  have na: "(norm a)\<^sup>2 = R^2 - b\<^sup>2"
    using norm_prod_def * real_sqrt_pow2
    by (metis add.commute add_diff_cancel_left' add_uminus_conv_diff fst_conv power2_abs real_norm_def 
real_sqrt_eq_iff real_sqrt_four real_sqrt_ge_0_iff snd_conv zero_le_numeral)
  define q where "q = norm ((C *\<^sub>R a) /\<^sub>R (R - b))"
  then have "q = \<bar>C/(R - b)\<bar> * norm a"
    apply (auto simp: q_def divide_simps \<open>b \<noteq> R\<close>). 
  then have "q\<^sup>2 = C\<^sup>2 * (R + b)/(R - b)"
    apply (auto simp: algebra_simps) sorry
    (* the proof above may require q_def na power2_eq_square square_diff_square_factored 
power2_abs \<open>b \<noteq> R\<close> divide_simps *)
  then have "q\<^sup>2 + C\<^sup>2 = 2 * R * C\<^sup>2/ (R - b)" sorry
  moreover have "q\<^sup>2 - C\<^sup>2 = 2 * C\<^sup>2 * b / (R - b)" sorry
  ultimately show "(4 * C * (inverse (R - b) * C) / ((\<bar>inverse (R - b) * C\<bar> * norm a)\<^sup>2 + C\<^sup>2)) *\<^sub>R a = a" sorry
  also show "(R * (\<bar>inverse (R - b) * C\<bar> * norm a)\<^sup>2 - R * C\<^sup>2) / ((\<bar>inverse (R - b) * C\<bar> * norm a)\<^sup>2 + C\<^sup>2) = b" sorry
qed

lemma (in rescaling) st_proj1_inv_inv: "st_proj1 (st_proj1_inv x) = x"
  apply transfer
  apply (auto simp: divide_simps)
  by (simp add: power2_eq_square)

lemma (in rescaling) st_proj1_inv_ne_top: "st_proj1_inv xa \<noteq> top_sphere"
  by transfer (auto simp: divide_simps add_nonneg_eq_0_iff)

lemma (in rescaling) homeomorphism_st_proj1: "homeomorphism (-{top_sphere}) UNIV st_proj1 st_proj1_inv"
  apply (auto simp: homeomorphism_def st_proj1_continuous st_proj1_inv_continuous st_proj1_inv_inv
      st_proj1_inv st_proj1_inv_ne_top)
  subgoal for x
    by (rule image_eqI[where x="st_proj1_inv x"]) (auto simp: st_proj1_inv_inv st_proj1_inv_ne_top)
  by (metis rangeI st_proj1_inv)

lemma (in rescaling) st_proj2_inv_continuous:
  "continuous_on UNIV st_proj2_inv"
  by transfer (auto intro!: continuous_intros simp: add_nonneg_eq_0_iff)

lemma (in rescaling) st_proj2_continuous:
  "continuous_on (UNIV -{bot_sphere}) st_proj2"
  apply (transfer; auto intro!: continuous_intros simp: add_nonneg_eq_0_iff split_beta' norm_prod_def)
proof -
  fix a b assume asm0: "sqrt((norm a)^2 + b^2) = R" and asm1: "R + b = 0"
  then show "a = 0"
  proof -
    have "b = -R" using asm1 by simp
    thus "a = 0"
      using asm0 by (metis add.commute norm_eq_zero power2_minus real_sqrt_sum_squares_eq_cancel)
  qed
qed

lemma (in rescaling) st_proj2_inv: "st_proj2_inv (st_proj2 x) = x"
  if "x \<noteq> bot_sphere"
  using that
  apply transfer
proof (clarsimp, rule conjI)
  fix a::'a and b::real
  assume *: "norm (a, b) = R" and ab: "a = 0 \<longrightarrow> b \<noteq> -R"
  then have "b \<noteq> -R" 
    using norm_prod_def
    by (metis add.commute norm_Pair norm_eq_zero norm_minus_cancel power2_abs real_norm_def real_sqrt_sum_squares_eq_cancel)
  then have "R + b \<noteq> 0" by auto
  then have "2*R + b * 2 \<noteq> 0" by auto
  have na: "(norm a)\<^sup>2 = R^2 - b\<^sup>2"
    using *
    unfolding norm_prod_def
    apply (auto simp: algebra_simps) 
    using real_sqrt_eq_iff by fastforce
  define S where "S = norm (a /\<^sub>R (R + b))"
  have "b = (R^2 - S\<^sup>2) / (S\<^sup>2 + R^2)"
    apply (auto simp: S_def divide_simps \<open>b \<noteq> -R\<close> na)
      apply (auto simp: power2_eq_square algebra_simps \<open>b \<noteq> -R\<close> \<open>R + b \<noteq> 0\<close> \<open>2*R + b * 2 \<noteq> 0\<close>)
    using \<open>b \<noteq> -R\<close> apply auto[3] sorry
  then show "(R - (inverse \<bar>R + b\<bar> * norm a)\<^sup>2) / ((inverse \<bar>R + b\<bar> * norm a)\<^sup>2 + R) = b"
    by (simp add: S_def)
  have "R = (2 / (R + b) / (S\<^sup>2 + R^2))"
    by (auto simp: S_def divide_simps \<open>b \<noteq> -R\<close> na)
       (auto simp: power2_eq_square algebra_simps \<open>b \<noteq> -R\<close> \<open>R + b \<noteq> 0\<close> \<open>2*R + b * 2 \<noteq> 0\<close>)
  then have "a = (2 / (R + b) / (S\<^sup>2 + R^2)) *\<^sub>R a"
    by simp 
  then show "(2 * inverse (R + b) / ((inverse \<bar>R + b\<bar> * norm a)\<^sup>2 + R^2)) *\<^sub>R a = a"
    by (auto simp: S_def divide_simps)
qed

lemma (in rescaling) st_proj2_inv_inv: "st_proj2 (st_proj2_inv x) = x"
  by transfer (auto simp: divide_simps add_nonneg_eq_0_iff)

lemma (in rescaling) st_proj2_inv_ne_top: "st_proj2_inv xa \<noteq> bot_sphere"
  by transfer (auto simp: divide_simps add_nonneg_eq_0_iff)

lemma (in rescaling) homeomorphism_st_proj2: "homeomorphism (UNIV - {bot_sphere}) UNIV st_proj2 st_proj2_inv"
  apply (auto simp: homeomorphism_def st_proj2_continuous st_proj2_inv_continuous st_proj2_inv_inv
      st_proj2_inv_def st_proj2_inv_ne_top)
  subgoal for x
    by (rule image_eqI[where x="st_proj2_inv x"]) (auto simp: st_proj2_inv_inv st_proj2_inv_ne_top)
  by (metis rangeI st_proj2_inv_def)

lift_definition (in rescaling) st_proj1_chart :: "('a sphere, 'a::euclidean_space) chart"
  is "(UNIV - {top_sphere::'a sphere}, UNIV::'a set, st_proj1, st_proj1_inv)"
  using homeomorphism_st_proj1 by blast
  
lift_definition (in rescaling) st_proj2_chart :: "('a sphere, 'a::euclidean_space) chart"
  is "(UNIV - {bot_sphere::'a sphere}, UNIV::'a set, st_proj2, st_proj2_inv)"
  using homeomorphism_st_proj2 by blast

lemma (in rescaling) st_projs_compat:
  includes lifting_syntax
  shows "\<infinity>-smooth_compat st_proj1_chart st_proj2_chart"
  unfolding smooth_compat_def
  apply (transfer; auto)
proof goal_cases
  case 1
  have *: "smooth_on ((\<lambda>(x::'a, z). x /\<^sub>R (R - z)) ` (({a. norm a = R} - {(0, R)}) \<inter> ({a. norm a = R} - {(0, - R)})))
     ((\<lambda>(x, z). x /\<^sub>R (R + z)) \<circ> (\<lambda>x. ((2 / ((norm x)\<^sup>2 + R^2)) *\<^sub>R x, ((norm x)\<^sup>2 - R^2) / ((norm x)\<^sup>2 + R^2))))"
    apply (rule smooth_on_subset[where T="UNIV - {0}"])
    subgoal
      by (auto intro!: smooth_on_divide smooth_on_inverse smooth_on_scaleR smooth_on_mult smooth_on_add
          smooth_on_minus smooth_on_norm simp: o_def power2_eq_square add_nonneg_eq_0_iff divide_simps)
    apply (auto simp: norm_prod_def power2_eq_square) apply sos
    done
  show ?case
    by transfer (rule *)
next
  case 2
  have *: "smooth_on ((\<lambda>(x::'a, z). x /\<^sub>R (R + z)) ` (({a. norm a = R} - {(0, R)}) \<inter> ({a. norm a = R} - {(0, - R)})))
     ((\<lambda>(x, z). x /\<^sub>R (R - z)) \<circ> (\<lambda>x. ((2 / ((norm x)\<^sup>2 + R^2)) *\<^sub>R x, (R^2 - (norm x)\<^sup>2) / ((norm x)\<^sup>2 + R^2))))"
    apply (rule smooth_on_subset[where T="UNIV - {0}"])
    subgoal
      by (auto intro!: smooth_on_divide smooth_on_inverse smooth_on_scaleR smooth_on_mult smooth_on_add
          smooth_on_minus smooth_on_norm simp: o_def power2_eq_square add_nonneg_eq_0_iff divide_simps)
    apply (auto simp: norm_prod_def add_eq_0_iff) apply sos
    done
  show ?case
    by transfer (rule *)
qed

definition (in rescaling) charts_sphere :: "('a::euclidean_space sphere, 'a) chart set" where
  "charts_sphere \<equiv> {st_proj1_chart, st_proj2_chart}"

lemma (in rescaling) c_manifold_atlas_sphere: "c_manifold charts_sphere \<infinity>"
  apply (unfold_locales)
  unfolding charts_sphere_def
  using smooth_compat_commute smooth_compat_refl st_projs_compat by fastforce

end
