theory Lie_Groups_3
imports 
  Main
  Smooth_Manifolds.Product_Manifold
  Smooth_Manifolds.Differentiable_Manifold
  Smooth_Manifolds.Tangent_Space
 (* 
  Some code is freely adapted from Clemens Ballarin's A Case Study in Basic Algebra 
  https://www.isa-afp.org/entries/Jacobson_Basic_Algebra.html
  *)
  
begin


section \<open>Monoids\<close>

locale monoid =
  fixes M and mult and unit ("\<one>")
  assumes mult_closed [intro, simp]: "\<lbrakk> a \<in> M; b \<in> M \<rbrakk> \<Longrightarrow> mult (a, b) \<in> M"
    and unit_closed [intro, simp]: "\<one> \<in> M"
    and assoc [intro]: "\<lbrakk> a \<in> M; b \<in> M; c \<in> M \<rbrakk> \<Longrightarrow> mult (mult (a, b), c) = mult (a, mult (b, c))"
    and l_unit [intro, simp]: "a \<in> M \<Longrightarrow> mult (\<one>, a) = a"
    and r_unit [intro, simp]: "a \<in> M \<Longrightarrow> mult (a, \<one>) = a"

begin

abbreviation multiplication (infixl "\<cdot>" 70) where
"multiplication a b \<equiv> mult (a, b)"

definition invertible where 
"a \<in> M \<Longrightarrow> invertible a \<longleftrightarrow> (\<exists>b \<in> M. a \<cdot> b = \<one> \<and> b \<cdot> a = \<one>)"

end 

locale submonoid = monoid +
  fixes N
  assumes subset [intro, simp]: "N \<subseteq> M"
    and sub_mult_closed: "\<lbrakk> a \<in> N; b \<in> N \<rbrakk> \<Longrightarrow> a \<cdot> b \<in> N"
    and sub_unit_closed: "\<one> \<in> N"

section \<open>Groups\<close>


locale group = monoid G mult unit for G and mult and unit ("\<one>") + 
  fixes inv ("_\<^sup>-\<^sup>1")
  assumes l_inv: "a \<in> G \<Longrightarrow> (a\<^sup>-\<^sup>1) \<cdot> a = \<one>"
    and r_inv: "a \<in> G \<Longrightarrow> a \<cdot> (a\<^sup>-\<^sup>1) = \<one>"

locale subgroup = group +
  fixes H
  assumes subset [intro, simp]: "H \<subseteq> G"
    and sub_mult_closed: "\<lbrakk> a \<in> H; b \<in> H \<rbrakk> \<Longrightarrow> a \<cdot> b \<in> H"
    and sub_unit_closed: "\<one> \<in> H" 
    and sub_inv_closed: "a \<in> H \<Longrightarrow> a\<^sup>-\<^sup>1 \<in> H"


subsection \<open>Subgroup Generated By a Subset\<close>

context group begin

inductive_set generate :: "'a set \<Rightarrow> 'a set"
  for H where
    unit:  "\<one> \<in> generate H"
  | incl: "a \<in> H \<Longrightarrow> a \<in> generate H"
  | inv:  "a \<in> H \<Longrightarrow> (a\<^sup>-\<^sup>1) \<in> generate H"
  | mult:  "a \<in> generate H \<Longrightarrow> b \<in> generate H \<Longrightarrow> a \<cdot> b \<in> generate H"

definition subgroup_generated :: "'a set \<Rightarrow> 'a set"
  where "subgroup_generated S = generate (G \<inter> S)"

lemma subgroup_generated_is_subgroup:
  fixes H
  shows "subgroup G mult unit inv (subgroup_generated H)" sorry

end (* group *)

subsection \<open>Right Cosets\<close>

context group begin

definition r_coset (infixl "|\<cdot>" 70) where "N |\<cdot> x = {h \<cdot> x | h. h \<in> N}"

end (* group *)


section \<open>Lie Groups\<close>

subsection \<open>Lie Groups\<close>

locale lie_group = c_manifold + is_group: group carrier mult unit inv for mult and unit and inv +
  assumes smooth_mult: "diff k (c_manifold_prod.prod_charts charts charts) charts mult"
    and smooth_inv: "diff k charts charts inv"

subsection \<open>Smooth Maps Between Lie Groups\<close>

locale lie_groups =
  src: lie_group charts1 k mult1 unit1 inv1 + 
  dest: lie_group charts2 k mult2 unit2 inv2 
  for k charts1 mult1 unit1 inv1 charts2 mult2 unit2 inv2

locale lie_diff = lie_groups k charts1 mult1 unit1 inv1 charts2 mult2 unit2 inv2
  for k 
    and charts1 :: "('a::{t2_space,second_countable_topology}, 'e::euclidean_space) chart set"
    and mult1 unit1 inv1
    and charts2 :: "('b::{t2_space,second_countable_topology}, 'f::euclidean_space) chart set"
    and mult2 unit2 inv2
    +
  fixes f :: "('a \<Rightarrow> 'b)"
  assumes exists_smooth_on: "x \<in> src.carrier \<Longrightarrow>
    \<exists>c1\<in>src.atlas. \<exists>c2\<in>dest.atlas.
      x \<in> domain c1 \<and>
      f ` domain c1 \<subseteq> domain c2 \<and>
      k-smooth_on (codomain c1) (c2 \<circ> f \<circ> inv_chart c1)"

locale lie_diffeomorphism = lie_diff k charts1 mult1 unit1 inv1 charts2 mult2 unit2 inv2 f + 
  inv: lie_diff k charts2 mult2 unit2 inv2 charts1 mult1 unit1 inv1 f'
  for k charts1 mult1 unit1 inv1 charts2 mult2 unit2 inv2 f f' +
  assumes f_inv[simp]:  "\<And>x. x \<in> src.carrier \<Longrightarrow> f' (f x) = x"
      and f'_inv[simp]: "\<And>y. y \<in> dest.carrier \<Longrightarrow> f (f' y) = y"

locale lie_group_map = lie_diffeomorphism k charts1 mult1 unit1 inv1 charts2 mult2 unit2 inv2 f f' 
  for k charts1 mult1 unit1 inv1 charts2 mult2 unit2 inv2 f f' +
  assumes map_mult: "f (mult1 (a, b)) = mult2 (f a, f b)"
    and map_unit: "f unit1 = unit2"


subsection "Lie Subgroups"

locale lie_subgroup = lie_group charts k mult unit inv
  for charts::"('a::{t2_space,second_countable_topology}, 'b::euclidean_space) chart set" and
    k and mult and unit and inv +
  fixes S::"'a set"
  assumes open_submanifold: "open S"
    and is_subgroup: "subgroup carrier mult unit inv (S \<inter> carrier)"

abbreviation (in lie_subgroup) subcarrier where
"subcarrier \<equiv> S \<inter> carrier"


subsection \<open>Connected Lie Groups\<close>

locale connected_lie_group = c_manifold + is_group: group carrier mult unit inv for mult and unit and inv +
  assumes smooth_mult: "diff k (c_manifold_prod.prod_charts charts charts) charts mult"
    and smooth_inv: "diff k charts charts inv"
    and is_connected: "connected carrier"

locale lie_subgroup_of_connected = connected_lie_group charts k mult unit inv
  for charts::"('a::{t2_space,second_countable_topology}, 'b::euclidean_space) chart set" and
    k and mult and unit and inv +
  fixes S::"'a set"
  assumes open_submanifold: "open S"
    and is_subgroup: "subgroup carrier mult unit inv (S \<inter> carrier)"

definition is_dense:: "'a topology \<Rightarrow> 'a set \<Rightarrow> bool" where (* It should be moved somewhere else *)
"is_dense T S \<equiv> topspace T \<subseteq> T closure_of S"

context lie_subgroup_of_connected begin

abbreviation subcarrier where
"subcarrier \<equiv> S \<inter> carrier"

lemma lie_subgroup_is_closed:
  shows "closed subcarrier"
proof-
  have "subgroup carrier mult unit inv (closure subcarrier)" sorry
  moreover have coset_open:
"\<forall>x\<in>(closure subcarrier). 
openin (subtopology (subtopology euclidean carrier) (closure subcarrier)) (subcarrier |\<cdot> x)" sorry
(*"\<forall>x\<in>(closure subcarrier).\<exists>U. open U \<and> (subcarrier |\<cdot> x = U \<inter> closure subcarrier)" *)
  moreover have coset_dense:
"\<forall>x\<in>(closure subcarrier). 
is_dense (subtopology (subtopology euclidean carrier) (closure subcarrier)) (subcarrier |\<cdot> x)" sorry
(*"\<forall>x\<in>(closure subcarrier).\<forall>y\<in>(closure subcarrier).\<forall>U. 
openin (subtopology (subtopology euclidean carrier) (closure subcarrier)) U \<and> y \<in> U \<longrightarrow>
(\<exists>z. z \<in> subcarrier |\<cdot> x \<inter> U)"*)
(*"\<forall>x\<in>(closure subcarrier).\<forall>y\<in>(closure subcarrier).\<forall>U. 
(open U \<and> y\<in>(U \<inter> closure subcarrier) \<longrightarrow> (\<exists>z. z \<in> ((subcarrier |\<cdot> x) \<inter> (U \<inter> closure subcarrier))))"*)
  ultimately have "closure subcarrier = subcarrier" sorry
  thus ?thesis by (metis closed_closure)
qed

end (* lie_subgroup_of_connected *)

lemma (in topological_space) clopen_of_connected_space: (* Should be moved somewhere else *)
  fixes S carrier
  assumes "S \<subseteq> carrier" and "connected carrier" and "S \<noteq> {}" and "open S" and "closed S"
  shows "S = carrier"
proof-
  {
  assume "S \<noteq> carrier"
  then have "carrier - S \<noteq> {}"
    using assms(1) by simp
  moreover have "carrier = S \<union> (carrier - S)"
    using assms(1) by auto
  moreover have "open (carrier - S)" using assms(1,4) closed_def
    by (smt Compl_Diff_eq Diff_disjoint Diff_eq Diff_eq_empty_iff Diff_triv Int_commute Un_upper2 assms(2,3,5) calculation(1) local.connected_def)
  ultimately have "False"
    using assms(2,3,4) local.connected_def by auto
  }
  thus ?thesis by auto
qed

context connected_lie_group begin

lemma closed_subgroup_is_lie_subgroup:
  fixes H
  assumes is_subgroup: "subgroup carrier mult unit inv H" and is_closed: "closed H"
  shows "lie_subgroup charts k mult unit inv H" sorry

lemma neighborhood_of_unit_generates:
  fixes U
  assumes "open U" and "unit \<in> U \<inter> carrier"
  shows "group.subgroup_generated carrier mult unit inv (U \<inter> carrier) = carrier"
proof-
  define H where "H = group.subgroup_generated carrier mult unit inv (U \<inter> carrier)"
  then have "\<forall>h\<in>H. h \<in> {mult (h,u)| u. u \<in> U}" sorry
  moreover have "\<forall>h\<in> H. open {mult (h,u)| u. u \<in> U}" sorry
  then have "open H"
  proof-
    have "H = (\<Union> h\<in>H. {mult (h,u)| u. u \<in> U})" sorry
    thus ?thesis
      using \<open>\<forall>h\<in>H. open {h \<cdot> u |u. u \<in> U}\<close> open_UN by fastforce
  qed
  moreover have "lie_subgroup_of_connected charts k mult unit inv H"
    using \<open>open H\<close> H_def group.subgroup_generated_is_subgroup
    by (metis connected_lie_group_axioms connected_lie_group_def inf.orderE lie_subgroup_of_connected.intro 
lie_subgroup_of_connected_axioms_def subgroup.subset) 
  then have "closed H"
    using lie_subgroup_of_connected.lie_subgroup_is_closed
    by (metis inf.absorb1 is_group.subgroup_generated_is_subgroup local.H_def subgroup.subset)
  ultimately show "H = carrier"
  proof-
    have "unit \<in> H" 
      using H_def is_group.generate.unit is_group.subgroup_generated_def by simp
    then have "H \<noteq> {}" by auto
    thus ?thesis
    proof-
      have "H \<subseteq> carrier" 
        using H_def by (meson is_group.subgroup_generated_is_subgroup subgroup.subset)
      thus ?thesis
        using is_connected clopen_of_connected_space \<open>open H\<close> \<open>closed H\<close> \<open>H \<noteq> {}\<close> by auto
    qed
  qed
qed

end (* connected_lie_group *)

context lie_group_map begin

lemma surjective_pushforward_of_map_with_connected_dest:
  assumes dest_is_connected: "connected_lie_group charts2 k mult2 unit2 inv2"
    and pushforward_is_surjective: 
"\<forall>Y\<in>(c_manifold.tangent_space charts2 k unit2).\<exists>X\<in>c_manifold.tangent_space charts1 k unit1. 
diff.push_forward k charts1 charts2 f X = Y"
  shows "surj f" sorry

end (* lie_group_map *)

end