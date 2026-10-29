import FiniteCertificate
import FullFormulaProperties

namespace Kunisky

def Tree.AllNonTautological {α : Type*} [DecidableEq α] : Tree α → Prop
  | .leaf C => NonTautological C
  | .node v l r => NonTautological (Tree.node v l r).conclusion ∧
      l.AllNonTautological ∧ r.AllNonTautological

namespace FiniteCounterexample

lemma noTaut0 : Tree.AllNonTautological t0 := by
  unfold t0 Tree.AllNonTautological NonTautological
  decide

lemma noTaut1 : Tree.AllNonTautological t1 := by
  unfold t1 Tree.AllNonTautological NonTautological
  decide

lemma noTaut2 : Tree.AllNonTautological t2 := by
  unfold t2 Tree.AllNonTautological NonTautological
  decide

lemma noTaut3 : Tree.AllNonTautological t3 := by
  unfold t3 Tree.AllNonTautological NonTautological
  decide

lemma noTaut4 : Tree.AllNonTautological t4 := by
  unfold t4 Tree.AllNonTautological NonTautological
  decide

lemma noTaut5 : Tree.AllNonTautological t5 := by
  unfold t5 Tree.AllNonTautological NonTautological
  decide

lemma noTaut6 : Tree.AllNonTautological t6 := by
  unfold t6 Tree.AllNonTautological NonTautological
  decide

lemma noTaut7 : Tree.AllNonTautological t7 := by
  unfold t7 Tree.AllNonTautological NonTautological
  decide

lemma noTaut8 : Tree.AllNonTautological t8 := by
  change NonTautological t8.conclusion ∧ t0.AllNonTautological ∧ t4.AllNonTautological
  refine ⟨?_, noTaut0, noTaut4⟩
  rw [cert8.2.1]
  unfold NonTautological
  decide

lemma noTaut9 : Tree.AllNonTautological t9 := by
  change NonTautological t9.conclusion ∧ t3.AllNonTautological ∧ t7.AllNonTautological
  refine ⟨?_, noTaut3, noTaut7⟩
  rw [cert9.2.1]
  unfold NonTautological
  decide

lemma noTaut10 : Tree.AllNonTautological t10 := by
  change NonTautological t10.conclusion ∧ t0.AllNonTautological ∧ t2.AllNonTautological
  refine ⟨?_, noTaut0, noTaut2⟩
  rw [cert10.2.1]
  unfold NonTautological
  decide

lemma noTaut11 : Tree.AllNonTautological t11 := by
  change NonTautological t11.conclusion ∧ t0.AllNonTautological ∧ t1.AllNonTautological
  refine ⟨?_, noTaut0, noTaut1⟩
  rw [cert11.2.1]
  unfold NonTautological
  decide

lemma noTaut12 : Tree.AllNonTautological t12 := by
  change NonTautological t12.conclusion ∧ t5.AllNonTautological ∧ t7.AllNonTautological
  refine ⟨?_, noTaut5, noTaut7⟩
  rw [cert12.2.1]
  unfold NonTautological
  decide

lemma noTaut13 : Tree.AllNonTautological t13 := by
  change NonTautological t13.conclusion ∧ t6.AllNonTautological ∧ t7.AllNonTautological
  refine ⟨?_, noTaut6, noTaut7⟩
  rw [cert13.2.1]
  unfold NonTautological
  decide

lemma noTaut14 : Tree.AllNonTautological t14 := by
  change NonTautological t14.conclusion ∧ t11.AllNonTautological ∧ t12.AllNonTautological
  refine ⟨?_, noTaut11, noTaut12⟩
  rw [cert14.2.1]
  unfold NonTautological
  decide

lemma noTaut15 : Tree.AllNonTautological t15 := by
  change NonTautological t15.conclusion ∧ t10.AllNonTautological ∧ t13.AllNonTautological
  refine ⟨?_, noTaut10, noTaut13⟩
  rw [cert15.2.1]
  unfold NonTautological
  decide

lemma noTaut16 : Tree.AllNonTautological t16 := by
  change NonTautological t16.conclusion ∧ t10.AllNonTautological ∧ t9.AllNonTautological
  refine ⟨?_, noTaut10, noTaut9⟩
  rw [cert16.2.1]
  unfold NonTautological
  decide

lemma noTaut17 : Tree.AllNonTautological t17 := by
  change NonTautological t17.conclusion ∧ t8.AllNonTautological ∧ t13.AllNonTautological
  refine ⟨?_, noTaut8, noTaut13⟩
  rw [cert17.2.1]
  unfold NonTautological
  decide

lemma noTaut18 : Tree.AllNonTautological t18 := by
  change NonTautological t18.conclusion ∧ t8.AllNonTautological ∧ t12.AllNonTautological
  refine ⟨?_, noTaut8, noTaut12⟩
  rw [cert18.2.1]
  unfold NonTautological
  decide

lemma noTaut19 : Tree.AllNonTautological t19 := by
  change NonTautological t19.conclusion ∧ t0.AllNonTautological ∧ t17.AllNonTautological
  refine ⟨?_, noTaut0, noTaut17⟩
  rw [cert19.2.1]
  unfold NonTautological
  decide

lemma noTaut20 : Tree.AllNonTautological t20 := by
  change NonTautological t20.conclusion ∧ t16.AllNonTautological ∧ t12.AllNonTautological
  refine ⟨?_, noTaut16, noTaut12⟩
  rw [cert20.2.1]
  unfold NonTautological
  decide

lemma noTaut21 : Tree.AllNonTautological t21 := by
  change NonTautological t21.conclusion ∧ t0.AllNonTautological ∧ t15.AllNonTautological
  refine ⟨?_, noTaut0, noTaut15⟩
  rw [cert21.2.1]
  unfold NonTautological
  decide

lemma noTaut22 : Tree.AllNonTautological t22 := by
  change NonTautological t22.conclusion ∧ t0.AllNonTautological ∧ t14.AllNonTautological
  refine ⟨?_, noTaut0, noTaut14⟩
  rw [cert22.2.1]
  unfold NonTautological
  decide

lemma noTaut23 : Tree.AllNonTautological t23 := by
  change NonTautological t23.conclusion ∧ t18.AllNonTautological ∧ t9.AllNonTautological
  refine ⟨?_, noTaut18, noTaut9⟩
  rw [cert23.2.1]
  unfold NonTautological
  decide

lemma noTaut24 : Tree.AllNonTautological t24 := by
  change NonTautological t24.conclusion ∧ t17.AllNonTautological ∧ t9.AllNonTautological
  refine ⟨?_, noTaut17, noTaut9⟩
  rw [cert24.2.1]
  unfold NonTautological
  decide

lemma noTaut25 : Tree.AllNonTautological t25 := by
  change NonTautological t25.conclusion ∧ t22.AllNonTautological ∧ t23.AllNonTautological
  refine ⟨?_, noTaut22, noTaut23⟩
  rw [cert25.2.1]
  unfold NonTautological
  decide

lemma noTaut26 : Tree.AllNonTautological t26 := by
  change NonTautological t26.conclusion ∧ t21.AllNonTautological ∧ t24.AllNonTautological
  refine ⟨?_, noTaut21, noTaut24⟩
  rw [cert26.2.1]
  unfold NonTautological
  decide

lemma noTaut27 : Tree.AllNonTautological t27 := by
  change NonTautological t27.conclusion ∧ t16.AllNonTautological ∧ t23.AllNonTautological
  refine ⟨?_, noTaut16, noTaut23⟩
  rw [cert27.2.1]
  unfold NonTautological
  decide

lemma noTaut28 : Tree.AllNonTautological t28 := by
  change NonTautological t28.conclusion ∧ t21.AllNonTautological ∧ t20.AllNonTautological
  refine ⟨?_, noTaut21, noTaut20⟩
  rw [cert28.2.1]
  unfold NonTautological
  decide

lemma noTaut29 : Tree.AllNonTautological t29 := by
  change NonTautological t29.conclusion ∧ t19.AllNonTautological ∧ t24.AllNonTautological
  refine ⟨?_, noTaut19, noTaut24⟩
  rw [cert29.2.1]
  unfold NonTautological
  decide

lemma noTaut30 : Tree.AllNonTautological t30 := by
  change NonTautological t30.conclusion ∧ t18.AllNonTautological ∧ t20.AllNonTautological
  refine ⟨?_, noTaut18, noTaut20⟩
  rw [cert30.2.1]
  unfold NonTautological
  decide

lemma noTaut31 : Tree.AllNonTautological t31 := by
  change NonTautological t31.conclusion ∧ t19.AllNonTautological ∧ t23.AllNonTautological
  refine ⟨?_, noTaut19, noTaut23⟩
  rw [cert31.2.1]
  unfold NonTautological
  decide

lemma noTaut32 : Tree.AllNonTautological t32 := by
  change NonTautological t32.conclusion ∧ t17.AllNonTautological ∧ t20.AllNonTautological
  refine ⟨?_, noTaut17, noTaut20⟩
  rw [cert32.2.1]
  unfold NonTautological
  decide

lemma noTaut33 : Tree.AllNonTautological t33 := by
  change NonTautological t33.conclusion ∧ t0.AllNonTautological ∧ t29.AllNonTautological
  refine ⟨?_, noTaut0, noTaut29⟩
  rw [cert33.2.1]
  unfold NonTautological
  decide

lemma noTaut34 : Tree.AllNonTautological t34 := by
  change NonTautological t34.conclusion ∧ t22.AllNonTautological ∧ t30.AllNonTautological
  refine ⟨?_, noTaut22, noTaut30⟩
  rw [cert34.2.1]
  unfold NonTautological
  decide

lemma noTaut35 : Tree.AllNonTautological t35 := by
  change NonTautological t35.conclusion ∧ t21.AllNonTautological ∧ t32.AllNonTautological
  refine ⟨?_, noTaut21, noTaut32⟩
  rw [cert35.2.1]
  unfold NonTautological
  decide

lemma noTaut36 : Tree.AllNonTautological t36 := by
  change NonTautological t36.conclusion ∧ t28.AllNonTautological ∧ t30.AllNonTautological
  refine ⟨?_, noTaut28, noTaut30⟩
  rw [cert36.2.1]
  unfold NonTautological
  decide

lemma noTaut37 : Tree.AllNonTautological t37 := by
  change NonTautological t37.conclusion ∧ t0.AllNonTautological ∧ t26.AllNonTautological
  refine ⟨?_, noTaut0, noTaut26⟩
  rw [cert37.2.1]
  unfold NonTautological
  decide

lemma noTaut38 : Tree.AllNonTautological t38 := by
  change NonTautological t38.conclusion ∧ t0.AllNonTautological ∧ t25.AllNonTautological
  refine ⟨?_, noTaut0, noTaut25⟩
  rw [cert38.2.1]
  unfold NonTautological
  decide

lemma noTaut39 : Tree.AllNonTautological t39 := by
  change NonTautological t39.conclusion ∧ t21.AllNonTautological ∧ t27.AllNonTautological
  refine ⟨?_, noTaut21, noTaut27⟩
  rw [cert39.2.1]
  unfold NonTautological
  decide

lemma noTaut40 : Tree.AllNonTautological t40 := by
  change NonTautological t40.conclusion ∧ t19.AllNonTautological ∧ t32.AllNonTautological
  refine ⟨?_, noTaut19, noTaut32⟩
  rw [cert40.2.1]
  unfold NonTautological
  decide

lemma noTaut41 : Tree.AllNonTautological t41 := by
  change NonTautological t41.conclusion ∧ t31.AllNonTautological ∧ t27.AllNonTautological
  refine ⟨?_, noTaut31, noTaut27⟩
  rw [cert41.2.1]
  unfold NonTautological
  decide

lemma noTaut42 : Tree.AllNonTautological t42 := by
  change NonTautological t42.conclusion ∧ t19.AllNonTautological ∧ t30.AllNonTautological
  refine ⟨?_, noTaut19, noTaut30⟩
  rw [cert42.2.1]
  unfold NonTautological
  decide

lemma noTaut43 : Tree.AllNonTautological t43 := by
  change NonTautological t43.conclusion ∧ t29.AllNonTautological ∧ t27.AllNonTautological
  refine ⟨?_, noTaut29, noTaut27⟩
  rw [cert43.2.1]
  unfold NonTautological
  decide

lemma noTaut44 : Tree.AllNonTautological t44 := by
  change NonTautological t44.conclusion ∧ t0.AllNonTautological ∧ t40.AllNonTautological
  refine ⟨?_, noTaut0, noTaut40⟩
  rw [cert44.2.1]
  unfold NonTautological
  decide

lemma noTaut45 : Tree.AllNonTautological t45 := by
  change NonTautological t45.conclusion ∧ t38.AllNonTautological ∧ t41.AllNonTautological
  refine ⟨?_, noTaut38, noTaut41⟩
  rw [cert45.2.1]
  unfold NonTautological
  decide

lemma noTaut46 : Tree.AllNonTautological t46 := by
  change NonTautological t46.conclusion ∧ t37.AllNonTautological ∧ t43.AllNonTautological
  refine ⟨?_, noTaut37, noTaut43⟩
  rw [cert46.2.1]
  unfold NonTautological
  decide

lemma noTaut47 : Tree.AllNonTautological t47 := by
  change NonTautological t47.conclusion ∧ t39.AllNonTautological ∧ t41.AllNonTautological
  refine ⟨?_, noTaut39, noTaut41⟩
  rw [cert47.2.1]
  unfold NonTautological
  decide

lemma noTaut48 : Tree.AllNonTautological t48 := by
  change NonTautological t48.conclusion ∧ t0.AllNonTautological ∧ t35.AllNonTautological
  refine ⟨?_, noTaut0, noTaut35⟩
  rw [cert48.2.1]
  unfold NonTautological
  decide

lemma noTaut49 : Tree.AllNonTautological t49 := by
  change NonTautological t49.conclusion ∧ t0.AllNonTautological ∧ t34.AllNonTautological
  refine ⟨?_, noTaut0, noTaut34⟩
  rw [cert49.2.1]
  unfold NonTautological
  decide

lemma noTaut50 : Tree.AllNonTautological t50 := by
  change NonTautological t50.conclusion ∧ t37.AllNonTautological ∧ t36.AllNonTautological
  refine ⟨?_, noTaut37, noTaut36⟩
  rw [cert50.2.1]
  unfold NonTautological
  decide

lemma noTaut51 : Tree.AllNonTautological t51 := by
  change NonTautological t51.conclusion ∧ t33.AllNonTautological ∧ t43.AllNonTautological
  refine ⟨?_, noTaut33, noTaut43⟩
  rw [cert51.2.1]
  unfold NonTautological
  decide

lemma noTaut52 : Tree.AllNonTautological t52 := by
  change NonTautological t52.conclusion ∧ t42.AllNonTautological ∧ t36.AllNonTautological
  refine ⟨?_, noTaut42, noTaut36⟩
  rw [cert52.2.1]
  unfold NonTautological
  decide

lemma noTaut53 : Tree.AllNonTautological t53 := by
  change NonTautological t53.conclusion ∧ t33.AllNonTautological ∧ t41.AllNonTautological
  refine ⟨?_, noTaut33, noTaut41⟩
  rw [cert53.2.1]
  unfold NonTautological
  decide

lemma noTaut54 : Tree.AllNonTautological t54 := by
  change NonTautological t54.conclusion ∧ t40.AllNonTautological ∧ t36.AllNonTautological
  refine ⟨?_, noTaut40, noTaut36⟩
  rw [cert54.2.1]
  unfold NonTautological
  decide

lemma noTaut55 : Tree.AllNonTautological t55 := by
  change NonTautological t55.conclusion ∧ t0.AllNonTautological ∧ t51.AllNonTautological
  refine ⟨?_, noTaut0, noTaut51⟩
  rw [cert55.2.1]
  unfold NonTautological
  decide

lemma noTaut56 : Tree.AllNonTautological t56 := by
  change NonTautological t56.conclusion ∧ t49.AllNonTautological ∧ t52.AllNonTautological
  refine ⟨?_, noTaut49, noTaut52⟩
  rw [cert56.2.1]
  unfold NonTautological
  decide

lemma noTaut57 : Tree.AllNonTautological t57 := by
  change NonTautological t57.conclusion ∧ t48.AllNonTautological ∧ t54.AllNonTautological
  refine ⟨?_, noTaut48, noTaut54⟩
  rw [cert57.2.1]
  unfold NonTautological
  decide

lemma noTaut58 : Tree.AllNonTautological t58 := by
  change NonTautological t58.conclusion ∧ t50.AllNonTautological ∧ t52.AllNonTautological
  refine ⟨?_, noTaut50, noTaut52⟩
  rw [cert58.2.1]
  unfold NonTautological
  decide

lemma noTaut59 : Tree.AllNonTautological t59 := by
  change NonTautological t59.conclusion ∧ t0.AllNonTautological ∧ t46.AllNonTautological
  refine ⟨?_, noTaut0, noTaut46⟩
  rw [cert59.2.1]
  unfold NonTautological
  decide

lemma noTaut60 : Tree.AllNonTautological t60 := by
  change NonTautological t60.conclusion ∧ t0.AllNonTautological ∧ t45.AllNonTautological
  refine ⟨?_, noTaut0, noTaut45⟩
  rw [cert60.2.1]
  unfold NonTautological
  decide

lemma noTaut61 : Tree.AllNonTautological t61 := by
  change NonTautological t61.conclusion ∧ t48.AllNonTautological ∧ t47.AllNonTautological
  refine ⟨?_, noTaut48, noTaut47⟩
  rw [cert61.2.1]
  unfold NonTautological
  decide

lemma noTaut62 : Tree.AllNonTautological t62 := by
  change NonTautological t62.conclusion ∧ t44.AllNonTautological ∧ t54.AllNonTautological
  refine ⟨?_, noTaut44, noTaut54⟩
  rw [cert62.2.1]
  unfold NonTautological
  decide

lemma noTaut63 : Tree.AllNonTautological t63 := by
  change NonTautological t63.conclusion ∧ t53.AllNonTautological ∧ t47.AllNonTautological
  refine ⟨?_, noTaut53, noTaut47⟩
  rw [cert63.2.1]
  unfold NonTautological
  decide

lemma noTaut64 : Tree.AllNonTautological t64 := by
  change NonTautological t64.conclusion ∧ t44.AllNonTautological ∧ t52.AllNonTautological
  refine ⟨?_, noTaut44, noTaut52⟩
  rw [cert64.2.1]
  unfold NonTautological
  decide

lemma noTaut65 : Tree.AllNonTautological t65 := by
  change NonTautological t65.conclusion ∧ t51.AllNonTautological ∧ t47.AllNonTautological
  refine ⟨?_, noTaut51, noTaut47⟩
  rw [cert65.2.1]
  unfold NonTautological
  decide

lemma noTaut66 : Tree.AllNonTautological t66 := by
  change NonTautological t66.conclusion ∧ t0.AllNonTautological ∧ t62.AllNonTautological
  refine ⟨?_, noTaut0, noTaut62⟩
  rw [cert66.2.1]
  unfold NonTautological
  decide

lemma noTaut67 : Tree.AllNonTautological t67 := by
  change NonTautological t67.conclusion ∧ t60.AllNonTautological ∧ t63.AllNonTautological
  refine ⟨?_, noTaut60, noTaut63⟩
  rw [cert67.2.1]
  unfold NonTautological
  decide

lemma noTaut68 : Tree.AllNonTautological t68 := by
  change NonTautological t68.conclusion ∧ t59.AllNonTautological ∧ t65.AllNonTautological
  refine ⟨?_, noTaut59, noTaut65⟩
  rw [cert68.2.1]
  unfold NonTautological
  decide

lemma noTaut69 : Tree.AllNonTautological t69 := by
  change NonTautological t69.conclusion ∧ t61.AllNonTautological ∧ t63.AllNonTautological
  refine ⟨?_, noTaut61, noTaut63⟩
  rw [cert69.2.1]
  unfold NonTautological
  decide

lemma noTaut70 : Tree.AllNonTautological t70 := by
  change NonTautological t70.conclusion ∧ t0.AllNonTautological ∧ t57.AllNonTautological
  refine ⟨?_, noTaut0, noTaut57⟩
  rw [cert70.2.1]
  unfold NonTautological
  decide

lemma noTaut71 : Tree.AllNonTautological t71 := by
  change NonTautological t71.conclusion ∧ t0.AllNonTautological ∧ t56.AllNonTautological
  refine ⟨?_, noTaut0, noTaut56⟩
  rw [cert71.2.1]
  unfold NonTautological
  decide

lemma noTaut72 : Tree.AllNonTautological t72 := by
  change NonTautological t72.conclusion ∧ t59.AllNonTautological ∧ t58.AllNonTautological
  refine ⟨?_, noTaut59, noTaut58⟩
  rw [cert72.2.1]
  unfold NonTautological
  decide

lemma noTaut73 : Tree.AllNonTautological t73 := by
  change NonTautological t73.conclusion ∧ t55.AllNonTautological ∧ t65.AllNonTautological
  refine ⟨?_, noTaut55, noTaut65⟩
  rw [cert73.2.1]
  unfold NonTautological
  decide

lemma noTaut74 : Tree.AllNonTautological t74 := by
  change NonTautological t74.conclusion ∧ t64.AllNonTautological ∧ t58.AllNonTautological
  refine ⟨?_, noTaut64, noTaut58⟩
  rw [cert74.2.1]
  unfold NonTautological
  decide

lemma noTaut75 : Tree.AllNonTautological t75 := by
  change NonTautological t75.conclusion ∧ t55.AllNonTautological ∧ t63.AllNonTautological
  refine ⟨?_, noTaut55, noTaut63⟩
  rw [cert75.2.1]
  unfold NonTautological
  decide

lemma noTaut76 : Tree.AllNonTautological t76 := by
  change NonTautological t76.conclusion ∧ t62.AllNonTautological ∧ t58.AllNonTautological
  refine ⟨?_, noTaut62, noTaut58⟩
  rw [cert76.2.1]
  unfold NonTautological
  decide

lemma noTaut77 : Tree.AllNonTautological t77 := by
  change NonTautological t77.conclusion ∧ t0.AllNonTautological ∧ t73.AllNonTautological
  refine ⟨?_, noTaut0, noTaut73⟩
  rw [cert77.2.1]
  unfold NonTautological
  decide

lemma noTaut78 : Tree.AllNonTautological t78 := by
  change NonTautological t78.conclusion ∧ t71.AllNonTautological ∧ t74.AllNonTautological
  refine ⟨?_, noTaut71, noTaut74⟩
  rw [cert78.2.1]
  unfold NonTautological
  decide

lemma noTaut79 : Tree.AllNonTautological t79 := by
  change NonTautological t79.conclusion ∧ t70.AllNonTautological ∧ t76.AllNonTautological
  refine ⟨?_, noTaut70, noTaut76⟩
  rw [cert79.2.1]
  unfold NonTautological
  decide

lemma noTaut80 : Tree.AllNonTautological t80 := by
  change NonTautological t80.conclusion ∧ t72.AllNonTautological ∧ t74.AllNonTautological
  refine ⟨?_, noTaut72, noTaut74⟩
  rw [cert80.2.1]
  unfold NonTautological
  decide

lemma noTaut81 : Tree.AllNonTautological t81 := by
  change NonTautological t81.conclusion ∧ t0.AllNonTautological ∧ t68.AllNonTautological
  refine ⟨?_, noTaut0, noTaut68⟩
  rw [cert81.2.1]
  unfold NonTautological
  decide

lemma noTaut82 : Tree.AllNonTautological t82 := by
  change NonTautological t82.conclusion ∧ t0.AllNonTautological ∧ t67.AllNonTautological
  refine ⟨?_, noTaut0, noTaut67⟩
  rw [cert82.2.1]
  unfold NonTautological
  decide

lemma noTaut83 : Tree.AllNonTautological t83 := by
  change NonTautological t83.conclusion ∧ t70.AllNonTautological ∧ t69.AllNonTautological
  refine ⟨?_, noTaut70, noTaut69⟩
  rw [cert83.2.1]
  unfold NonTautological
  decide

lemma noTaut84 : Tree.AllNonTautological t84 := by
  change NonTautological t84.conclusion ∧ t66.AllNonTautological ∧ t76.AllNonTautological
  refine ⟨?_, noTaut66, noTaut76⟩
  rw [cert84.2.1]
  unfold NonTautological
  decide

lemma noTaut85 : Tree.AllNonTautological t85 := by
  change NonTautological t85.conclusion ∧ t75.AllNonTautological ∧ t69.AllNonTautological
  refine ⟨?_, noTaut75, noTaut69⟩
  rw [cert85.2.1]
  unfold NonTautological
  decide

lemma noTaut86 : Tree.AllNonTautological t86 := by
  change NonTautological t86.conclusion ∧ t66.AllNonTautological ∧ t74.AllNonTautological
  refine ⟨?_, noTaut66, noTaut74⟩
  rw [cert86.2.1]
  unfold NonTautological
  decide

lemma noTaut87 : Tree.AllNonTautological t87 := by
  change NonTautological t87.conclusion ∧ t73.AllNonTautological ∧ t69.AllNonTautological
  refine ⟨?_, noTaut73, noTaut69⟩
  rw [cert87.2.1]
  unfold NonTautological
  decide

lemma noTaut88 : Tree.AllNonTautological t88 := by
  change NonTautological t88.conclusion ∧ t0.AllNonTautological ∧ t84.AllNonTautological
  refine ⟨?_, noTaut0, noTaut84⟩
  rw [cert88.2.1]
  unfold NonTautological
  decide

lemma noTaut89 : Tree.AllNonTautological t89 := by
  change NonTautological t89.conclusion ∧ t82.AllNonTautological ∧ t85.AllNonTautological
  refine ⟨?_, noTaut82, noTaut85⟩
  rw [cert89.2.1]
  unfold NonTautological
  decide

lemma noTaut90 : Tree.AllNonTautological t90 := by
  change NonTautological t90.conclusion ∧ t81.AllNonTautological ∧ t87.AllNonTautological
  refine ⟨?_, noTaut81, noTaut87⟩
  rw [cert90.2.1]
  unfold NonTautological
  decide

lemma noTaut91 : Tree.AllNonTautological t91 := by
  change NonTautological t91.conclusion ∧ t83.AllNonTautological ∧ t85.AllNonTautological
  refine ⟨?_, noTaut83, noTaut85⟩
  rw [cert91.2.1]
  unfold NonTautological
  decide

lemma noTaut92 : Tree.AllNonTautological t92 := by
  change NonTautological t92.conclusion ∧ t0.AllNonTautological ∧ t79.AllNonTautological
  refine ⟨?_, noTaut0, noTaut79⟩
  rw [cert92.2.1]
  unfold NonTautological
  decide

lemma noTaut93 : Tree.AllNonTautological t93 := by
  change NonTautological t93.conclusion ∧ t0.AllNonTautological ∧ t78.AllNonTautological
  refine ⟨?_, noTaut0, noTaut78⟩
  rw [cert93.2.1]
  unfold NonTautological
  decide

lemma noTaut94 : Tree.AllNonTautological t94 := by
  change NonTautological t94.conclusion ∧ t81.AllNonTautological ∧ t80.AllNonTautological
  refine ⟨?_, noTaut81, noTaut80⟩
  rw [cert94.2.1]
  unfold NonTautological
  decide

lemma noTaut95 : Tree.AllNonTautological t95 := by
  change NonTautological t95.conclusion ∧ t77.AllNonTautological ∧ t87.AllNonTautological
  refine ⟨?_, noTaut77, noTaut87⟩
  rw [cert95.2.1]
  unfold NonTautological
  decide

lemma noTaut96 : Tree.AllNonTautological t96 := by
  change NonTautological t96.conclusion ∧ t86.AllNonTautological ∧ t80.AllNonTautological
  refine ⟨?_, noTaut86, noTaut80⟩
  rw [cert96.2.1]
  unfold NonTautological
  decide

lemma noTaut97 : Tree.AllNonTautological t97 := by
  change NonTautological t97.conclusion ∧ t77.AllNonTautological ∧ t85.AllNonTautological
  refine ⟨?_, noTaut77, noTaut85⟩
  rw [cert97.2.1]
  unfold NonTautological
  decide

lemma noTaut98 : Tree.AllNonTautological t98 := by
  change NonTautological t98.conclusion ∧ t84.AllNonTautological ∧ t80.AllNonTautological
  refine ⟨?_, noTaut84, noTaut80⟩
  rw [cert98.2.1]
  unfold NonTautological
  decide

lemma noTaut99 : Tree.AllNonTautological t99 := by
  change NonTautological t99.conclusion ∧ t0.AllNonTautological ∧ t95.AllNonTautological
  refine ⟨?_, noTaut0, noTaut95⟩
  rw [cert99.2.1]
  unfold NonTautological
  decide

lemma noTaut100 : Tree.AllNonTautological t100 := by
  change NonTautological t100.conclusion ∧ t93.AllNonTautological ∧ t96.AllNonTautological
  refine ⟨?_, noTaut93, noTaut96⟩
  rw [cert100.2.1]
  unfold NonTautological
  decide

lemma noTaut101 : Tree.AllNonTautological t101 := by
  change NonTautological t101.conclusion ∧ t92.AllNonTautological ∧ t98.AllNonTautological
  refine ⟨?_, noTaut92, noTaut98⟩
  rw [cert101.2.1]
  unfold NonTautological
  decide

lemma noTaut102 : Tree.AllNonTautological t102 := by
  change NonTautological t102.conclusion ∧ t94.AllNonTautological ∧ t96.AllNonTautological
  refine ⟨?_, noTaut94, noTaut96⟩
  rw [cert102.2.1]
  unfold NonTautological
  decide

lemma noTaut103 : Tree.AllNonTautological t103 := by
  change NonTautological t103.conclusion ∧ t0.AllNonTautological ∧ t90.AllNonTautological
  refine ⟨?_, noTaut0, noTaut90⟩
  rw [cert103.2.1]
  unfold NonTautological
  decide

lemma noTaut104 : Tree.AllNonTautological t104 := by
  change NonTautological t104.conclusion ∧ t0.AllNonTautological ∧ t89.AllNonTautological
  refine ⟨?_, noTaut0, noTaut89⟩
  rw [cert104.2.1]
  unfold NonTautological
  decide

lemma noTaut105 : Tree.AllNonTautological t105 := by
  change NonTautological t105.conclusion ∧ t92.AllNonTautological ∧ t91.AllNonTautological
  refine ⟨?_, noTaut92, noTaut91⟩
  rw [cert105.2.1]
  unfold NonTautological
  decide

lemma noTaut106 : Tree.AllNonTautological t106 := by
  change NonTautological t106.conclusion ∧ t88.AllNonTautological ∧ t98.AllNonTautological
  refine ⟨?_, noTaut88, noTaut98⟩
  rw [cert106.2.1]
  unfold NonTautological
  decide

lemma noTaut107 : Tree.AllNonTautological t107 := by
  change NonTautological t107.conclusion ∧ t97.AllNonTautological ∧ t91.AllNonTautological
  refine ⟨?_, noTaut97, noTaut91⟩
  rw [cert107.2.1]
  unfold NonTautological
  decide

lemma noTaut108 : Tree.AllNonTautological t108 := by
  change NonTautological t108.conclusion ∧ t88.AllNonTautological ∧ t96.AllNonTautological
  refine ⟨?_, noTaut88, noTaut96⟩
  rw [cert108.2.1]
  unfold NonTautological
  decide

lemma noTaut109 : Tree.AllNonTautological t109 := by
  change NonTautological t109.conclusion ∧ t95.AllNonTautological ∧ t91.AllNonTautological
  refine ⟨?_, noTaut95, noTaut91⟩
  rw [cert109.2.1]
  unfold NonTautological
  decide

lemma noTaut110 : Tree.AllNonTautological t110 := by
  change NonTautological t110.conclusion ∧ t0.AllNonTautological ∧ t106.AllNonTautological
  refine ⟨?_, noTaut0, noTaut106⟩
  rw [cert110.2.1]
  unfold NonTautological
  decide

lemma noTaut111 : Tree.AllNonTautological t111 := by
  change NonTautological t111.conclusion ∧ t104.AllNonTautological ∧ t107.AllNonTautological
  refine ⟨?_, noTaut104, noTaut107⟩
  rw [cert111.2.1]
  unfold NonTautological
  decide

lemma noTaut112 : Tree.AllNonTautological t112 := by
  change NonTautological t112.conclusion ∧ t103.AllNonTautological ∧ t109.AllNonTautological
  refine ⟨?_, noTaut103, noTaut109⟩
  rw [cert112.2.1]
  unfold NonTautological
  decide

lemma noTaut113 : Tree.AllNonTautological t113 := by
  change NonTautological t113.conclusion ∧ t105.AllNonTautological ∧ t107.AllNonTautological
  refine ⟨?_, noTaut105, noTaut107⟩
  rw [cert113.2.1]
  unfold NonTautological
  decide

lemma noTaut114 : Tree.AllNonTautological t114 := by
  change NonTautological t114.conclusion ∧ t0.AllNonTautological ∧ t101.AllNonTautological
  refine ⟨?_, noTaut0, noTaut101⟩
  rw [cert114.2.1]
  unfold NonTautological
  decide

lemma noTaut115 : Tree.AllNonTautological t115 := by
  change NonTautological t115.conclusion ∧ t0.AllNonTautological ∧ t100.AllNonTautological
  refine ⟨?_, noTaut0, noTaut100⟩
  rw [cert115.2.1]
  unfold NonTautological
  decide

lemma noTaut116 : Tree.AllNonTautological t116 := by
  change NonTautological t116.conclusion ∧ t103.AllNonTautological ∧ t102.AllNonTautological
  refine ⟨?_, noTaut103, noTaut102⟩
  rw [cert116.2.1]
  unfold NonTautological
  decide

lemma noTaut117 : Tree.AllNonTautological t117 := by
  change NonTautological t117.conclusion ∧ t99.AllNonTautological ∧ t109.AllNonTautological
  refine ⟨?_, noTaut99, noTaut109⟩
  rw [cert117.2.1]
  unfold NonTautological
  decide

lemma noTaut118 : Tree.AllNonTautological t118 := by
  change NonTautological t118.conclusion ∧ t108.AllNonTautological ∧ t102.AllNonTautological
  refine ⟨?_, noTaut108, noTaut102⟩
  rw [cert118.2.1]
  unfold NonTautological
  decide

lemma noTaut119 : Tree.AllNonTautological t119 := by
  change NonTautological t119.conclusion ∧ t99.AllNonTautological ∧ t107.AllNonTautological
  refine ⟨?_, noTaut99, noTaut107⟩
  rw [cert119.2.1]
  unfold NonTautological
  decide

lemma noTaut120 : Tree.AllNonTautological t120 := by
  change NonTautological t120.conclusion ∧ t106.AllNonTautological ∧ t102.AllNonTautological
  refine ⟨?_, noTaut106, noTaut102⟩
  rw [cert120.2.1]
  unfold NonTautological
  decide

lemma noTaut121 : Tree.AllNonTautological t121 := by
  change NonTautological t121.conclusion ∧ t0.AllNonTautological ∧ t117.AllNonTautological
  refine ⟨?_, noTaut0, noTaut117⟩
  rw [cert121.2.1]
  unfold NonTautological
  decide

lemma noTaut122 : Tree.AllNonTautological t122 := by
  change NonTautological t122.conclusion ∧ t115.AllNonTautological ∧ t118.AllNonTautological
  refine ⟨?_, noTaut115, noTaut118⟩
  rw [cert122.2.1]
  unfold NonTautological
  decide

lemma noTaut123 : Tree.AllNonTautological t123 := by
  change NonTautological t123.conclusion ∧ t114.AllNonTautological ∧ t120.AllNonTautological
  refine ⟨?_, noTaut114, noTaut120⟩
  rw [cert123.2.1]
  unfold NonTautological
  decide

lemma noTaut124 : Tree.AllNonTautological t124 := by
  change NonTautological t124.conclusion ∧ t116.AllNonTautological ∧ t118.AllNonTautological
  refine ⟨?_, noTaut116, noTaut118⟩
  rw [cert124.2.1]
  unfold NonTautological
  decide

lemma noTaut125 : Tree.AllNonTautological t125 := by
  change NonTautological t125.conclusion ∧ t0.AllNonTautological ∧ t112.AllNonTautological
  refine ⟨?_, noTaut0, noTaut112⟩
  rw [cert125.2.1]
  unfold NonTautological
  decide

lemma noTaut126 : Tree.AllNonTautological t126 := by
  change NonTautological t126.conclusion ∧ t0.AllNonTautological ∧ t111.AllNonTautological
  refine ⟨?_, noTaut0, noTaut111⟩
  rw [cert126.2.1]
  unfold NonTautological
  decide

lemma noTaut127 : Tree.AllNonTautological t127 := by
  change NonTautological t127.conclusion ∧ t114.AllNonTautological ∧ t113.AllNonTautological
  refine ⟨?_, noTaut114, noTaut113⟩
  rw [cert127.2.1]
  unfold NonTautological
  decide

lemma noTaut128 : Tree.AllNonTautological t128 := by
  change NonTautological t128.conclusion ∧ t110.AllNonTautological ∧ t120.AllNonTautological
  refine ⟨?_, noTaut110, noTaut120⟩
  rw [cert128.2.1]
  unfold NonTautological
  decide

lemma noTaut129 : Tree.AllNonTautological t129 := by
  change NonTautological t129.conclusion ∧ t119.AllNonTautological ∧ t113.AllNonTautological
  refine ⟨?_, noTaut119, noTaut113⟩
  rw [cert129.2.1]
  unfold NonTautological
  decide

lemma noTaut130 : Tree.AllNonTautological t130 := by
  change NonTautological t130.conclusion ∧ t110.AllNonTautological ∧ t118.AllNonTautological
  refine ⟨?_, noTaut110, noTaut118⟩
  rw [cert130.2.1]
  unfold NonTautological
  decide

lemma noTaut131 : Tree.AllNonTautological t131 := by
  change NonTautological t131.conclusion ∧ t117.AllNonTautological ∧ t113.AllNonTautological
  refine ⟨?_, noTaut117, noTaut113⟩
  rw [cert131.2.1]
  unfold NonTautological
  decide

lemma noTaut132 : Tree.AllNonTautological t132 := by
  change NonTautological t132.conclusion ∧ t0.AllNonTautological ∧ t128.AllNonTautological
  refine ⟨?_, noTaut0, noTaut128⟩
  rw [cert132.2.1]
  unfold NonTautological
  decide

lemma noTaut133 : Tree.AllNonTautological t133 := by
  change NonTautological t133.conclusion ∧ t126.AllNonTautological ∧ t129.AllNonTautological
  refine ⟨?_, noTaut126, noTaut129⟩
  rw [cert133.2.1]
  unfold NonTautological
  decide

lemma noTaut134 : Tree.AllNonTautological t134 := by
  change NonTautological t134.conclusion ∧ t125.AllNonTautological ∧ t131.AllNonTautological
  refine ⟨?_, noTaut125, noTaut131⟩
  rw [cert134.2.1]
  unfold NonTautological
  decide

lemma noTaut135 : Tree.AllNonTautological t135 := by
  change NonTautological t135.conclusion ∧ t127.AllNonTautological ∧ t129.AllNonTautological
  refine ⟨?_, noTaut127, noTaut129⟩
  rw [cert135.2.1]
  unfold NonTautological
  decide

lemma noTaut136 : Tree.AllNonTautological t136 := by
  change NonTautological t136.conclusion ∧ t0.AllNonTautological ∧ t123.AllNonTautological
  refine ⟨?_, noTaut0, noTaut123⟩
  rw [cert136.2.1]
  unfold NonTautological
  decide

lemma noTaut137 : Tree.AllNonTautological t137 := by
  change NonTautological t137.conclusion ∧ t0.AllNonTautological ∧ t122.AllNonTautological
  refine ⟨?_, noTaut0, noTaut122⟩
  rw [cert137.2.1]
  unfold NonTautological
  decide

lemma noTaut138 : Tree.AllNonTautological t138 := by
  change NonTautological t138.conclusion ∧ t125.AllNonTautological ∧ t124.AllNonTautological
  refine ⟨?_, noTaut125, noTaut124⟩
  rw [cert138.2.1]
  unfold NonTautological
  decide

lemma noTaut139 : Tree.AllNonTautological t139 := by
  change NonTautological t139.conclusion ∧ t121.AllNonTautological ∧ t131.AllNonTautological
  refine ⟨?_, noTaut121, noTaut131⟩
  rw [cert139.2.1]
  unfold NonTautological
  decide

lemma noTaut140 : Tree.AllNonTautological t140 := by
  change NonTautological t140.conclusion ∧ t130.AllNonTautological ∧ t124.AllNonTautological
  refine ⟨?_, noTaut130, noTaut124⟩
  rw [cert140.2.1]
  unfold NonTautological
  decide

lemma noTaut141 : Tree.AllNonTautological t141 := by
  change NonTautological t141.conclusion ∧ t121.AllNonTautological ∧ t129.AllNonTautological
  refine ⟨?_, noTaut121, noTaut129⟩
  rw [cert141.2.1]
  unfold NonTautological
  decide

lemma noTaut142 : Tree.AllNonTautological t142 := by
  change NonTautological t142.conclusion ∧ t128.AllNonTautological ∧ t124.AllNonTautological
  refine ⟨?_, noTaut128, noTaut124⟩
  rw [cert142.2.1]
  unfold NonTautological
  decide

lemma noTaut143 : Tree.AllNonTautological t143 := by
  change NonTautological t143.conclusion ∧ t0.AllNonTautological ∧ t139.AllNonTautological
  refine ⟨?_, noTaut0, noTaut139⟩
  rw [cert143.2.1]
  unfold NonTautological
  decide

lemma noTaut144 : Tree.AllNonTautological t144 := by
  change NonTautological t144.conclusion ∧ t137.AllNonTautological ∧ t140.AllNonTautological
  refine ⟨?_, noTaut137, noTaut140⟩
  rw [cert144.2.1]
  unfold NonTautological
  decide

lemma noTaut145 : Tree.AllNonTautological t145 := by
  change NonTautological t145.conclusion ∧ t136.AllNonTautological ∧ t142.AllNonTautological
  refine ⟨?_, noTaut136, noTaut142⟩
  rw [cert145.2.1]
  unfold NonTautological
  decide

lemma noTaut146 : Tree.AllNonTautological t146 := by
  change NonTautological t146.conclusion ∧ t138.AllNonTautological ∧ t140.AllNonTautological
  refine ⟨?_, noTaut138, noTaut140⟩
  rw [cert146.2.1]
  unfold NonTautological
  decide

lemma noTaut147 : Tree.AllNonTautological t147 := by
  change NonTautological t147.conclusion ∧ t0.AllNonTautological ∧ t134.AllNonTautological
  refine ⟨?_, noTaut0, noTaut134⟩
  rw [cert147.2.1]
  unfold NonTautological
  decide

lemma noTaut148 : Tree.AllNonTautological t148 := by
  change NonTautological t148.conclusion ∧ t0.AllNonTautological ∧ t133.AllNonTautological
  refine ⟨?_, noTaut0, noTaut133⟩
  rw [cert148.2.1]
  unfold NonTautological
  decide

lemma noTaut149 : Tree.AllNonTautological t149 := by
  change NonTautological t149.conclusion ∧ t136.AllNonTautological ∧ t135.AllNonTautological
  refine ⟨?_, noTaut136, noTaut135⟩
  rw [cert149.2.1]
  unfold NonTautological
  decide

lemma noTaut150 : Tree.AllNonTautological t150 := by
  change NonTautological t150.conclusion ∧ t132.AllNonTautological ∧ t142.AllNonTautological
  refine ⟨?_, noTaut132, noTaut142⟩
  rw [cert150.2.1]
  unfold NonTautological
  decide

lemma noTaut151 : Tree.AllNonTautological t151 := by
  change NonTautological t151.conclusion ∧ t141.AllNonTautological ∧ t135.AllNonTautological
  refine ⟨?_, noTaut141, noTaut135⟩
  rw [cert151.2.1]
  unfold NonTautological
  decide

lemma noTaut152 : Tree.AllNonTautological t152 := by
  change NonTautological t152.conclusion ∧ t132.AllNonTautological ∧ t140.AllNonTautological
  refine ⟨?_, noTaut132, noTaut140⟩
  rw [cert152.2.1]
  unfold NonTautological
  decide

lemma noTaut153 : Tree.AllNonTautological t153 := by
  change NonTautological t153.conclusion ∧ t139.AllNonTautological ∧ t135.AllNonTautological
  refine ⟨?_, noTaut139, noTaut135⟩
  rw [cert153.2.1]
  unfold NonTautological
  decide

lemma noTaut154 : Tree.AllNonTautological t154 := by
  change NonTautological t154.conclusion ∧ t0.AllNonTautological ∧ t150.AllNonTautological
  refine ⟨?_, noTaut0, noTaut150⟩
  rw [cert154.2.1]
  unfold NonTautological
  decide

lemma noTaut155 : Tree.AllNonTautological t155 := by
  change NonTautological t155.conclusion ∧ t148.AllNonTautological ∧ t151.AllNonTautological
  refine ⟨?_, noTaut148, noTaut151⟩
  rw [cert155.2.1]
  unfold NonTautological
  decide

lemma noTaut156 : Tree.AllNonTautological t156 := by
  change NonTautological t156.conclusion ∧ t147.AllNonTautological ∧ t153.AllNonTautological
  refine ⟨?_, noTaut147, noTaut153⟩
  rw [cert156.2.1]
  unfold NonTautological
  decide

lemma noTaut157 : Tree.AllNonTautological t157 := by
  change NonTautological t157.conclusion ∧ t149.AllNonTautological ∧ t151.AllNonTautological
  refine ⟨?_, noTaut149, noTaut151⟩
  rw [cert157.2.1]
  unfold NonTautological
  decide

lemma noTaut158 : Tree.AllNonTautological t158 := by
  change NonTautological t158.conclusion ∧ t0.AllNonTautological ∧ t145.AllNonTautological
  refine ⟨?_, noTaut0, noTaut145⟩
  rw [cert158.2.1]
  unfold NonTautological
  decide

lemma noTaut159 : Tree.AllNonTautological t159 := by
  change NonTautological t159.conclusion ∧ t0.AllNonTautological ∧ t144.AllNonTautological
  refine ⟨?_, noTaut0, noTaut144⟩
  rw [cert159.2.1]
  unfold NonTautological
  decide

lemma noTaut160 : Tree.AllNonTautological t160 := by
  change NonTautological t160.conclusion ∧ t147.AllNonTautological ∧ t146.AllNonTautological
  refine ⟨?_, noTaut147, noTaut146⟩
  rw [cert160.2.1]
  unfold NonTautological
  decide

lemma noTaut161 : Tree.AllNonTautological t161 := by
  change NonTautological t161.conclusion ∧ t143.AllNonTautological ∧ t153.AllNonTautological
  refine ⟨?_, noTaut143, noTaut153⟩
  rw [cert161.2.1]
  unfold NonTautological
  decide

lemma noTaut162 : Tree.AllNonTautological t162 := by
  change NonTautological t162.conclusion ∧ t152.AllNonTautological ∧ t146.AllNonTautological
  refine ⟨?_, noTaut152, noTaut146⟩
  rw [cert162.2.1]
  unfold NonTautological
  decide

lemma noTaut163 : Tree.AllNonTautological t163 := by
  change NonTautological t163.conclusion ∧ t143.AllNonTautological ∧ t151.AllNonTautological
  refine ⟨?_, noTaut143, noTaut151⟩
  rw [cert163.2.1]
  unfold NonTautological
  decide

lemma noTaut164 : Tree.AllNonTautological t164 := by
  change NonTautological t164.conclusion ∧ t150.AllNonTautological ∧ t146.AllNonTautological
  refine ⟨?_, noTaut150, noTaut146⟩
  rw [cert164.2.1]
  unfold NonTautological
  decide

lemma noTaut165 : Tree.AllNonTautological t165 := by
  change NonTautological t165.conclusion ∧ t0.AllNonTautological ∧ t161.AllNonTautological
  refine ⟨?_, noTaut0, noTaut161⟩
  rw [cert165.2.1]
  unfold NonTautological
  decide

lemma noTaut166 : Tree.AllNonTautological t166 := by
  change NonTautological t166.conclusion ∧ t159.AllNonTautological ∧ t162.AllNonTautological
  refine ⟨?_, noTaut159, noTaut162⟩
  rw [cert166.2.1]
  unfold NonTautological
  decide

lemma noTaut167 : Tree.AllNonTautological t167 := by
  change NonTautological t167.conclusion ∧ t158.AllNonTautological ∧ t164.AllNonTautological
  refine ⟨?_, noTaut158, noTaut164⟩
  rw [cert167.2.1]
  unfold NonTautological
  decide

lemma noTaut168 : Tree.AllNonTautological t168 := by
  change NonTautological t168.conclusion ∧ t160.AllNonTautological ∧ t162.AllNonTautological
  refine ⟨?_, noTaut160, noTaut162⟩
  rw [cert168.2.1]
  unfold NonTautological
  decide

lemma noTaut169 : Tree.AllNonTautological t169 := by
  change NonTautological t169.conclusion ∧ t0.AllNonTautological ∧ t156.AllNonTautological
  refine ⟨?_, noTaut0, noTaut156⟩
  rw [cert169.2.1]
  unfold NonTautological
  decide

lemma noTaut170 : Tree.AllNonTautological t170 := by
  change NonTautological t170.conclusion ∧ t0.AllNonTautological ∧ t155.AllNonTautological
  refine ⟨?_, noTaut0, noTaut155⟩
  rw [cert170.2.1]
  unfold NonTautological
  decide

lemma noTaut171 : Tree.AllNonTautological t171 := by
  change NonTautological t171.conclusion ∧ t158.AllNonTautological ∧ t157.AllNonTautological
  refine ⟨?_, noTaut158, noTaut157⟩
  rw [cert171.2.1]
  unfold NonTautological
  decide

lemma noTaut172 : Tree.AllNonTautological t172 := by
  change NonTautological t172.conclusion ∧ t154.AllNonTautological ∧ t164.AllNonTautological
  refine ⟨?_, noTaut154, noTaut164⟩
  rw [cert172.2.1]
  unfold NonTautological
  decide

lemma noTaut173 : Tree.AllNonTautological t173 := by
  change NonTautological t173.conclusion ∧ t163.AllNonTautological ∧ t157.AllNonTautological
  refine ⟨?_, noTaut163, noTaut157⟩
  rw [cert173.2.1]
  unfold NonTautological
  decide

lemma noTaut174 : Tree.AllNonTautological t174 := by
  change NonTautological t174.conclusion ∧ t154.AllNonTautological ∧ t162.AllNonTautological
  refine ⟨?_, noTaut154, noTaut162⟩
  rw [cert174.2.1]
  unfold NonTautological
  decide

lemma noTaut175 : Tree.AllNonTautological t175 := by
  change NonTautological t175.conclusion ∧ t161.AllNonTautological ∧ t157.AllNonTautological
  refine ⟨?_, noTaut161, noTaut157⟩
  rw [cert175.2.1]
  unfold NonTautological
  decide

lemma noTaut176 : Tree.AllNonTautological t176 := by
  change NonTautological t176.conclusion ∧ t0.AllNonTautological ∧ t172.AllNonTautological
  refine ⟨?_, noTaut0, noTaut172⟩
  rw [cert176.2.1]
  unfold NonTautological
  decide

lemma noTaut177 : Tree.AllNonTautological t177 := by
  change NonTautological t177.conclusion ∧ t170.AllNonTautological ∧ t173.AllNonTautological
  refine ⟨?_, noTaut170, noTaut173⟩
  rw [cert177.2.1]
  unfold NonTautological
  decide

lemma noTaut178 : Tree.AllNonTautological t178 := by
  change NonTautological t178.conclusion ∧ t171.AllNonTautological ∧ t173.AllNonTautological
  refine ⟨?_, noTaut171, noTaut173⟩
  rw [cert178.2.1]
  unfold NonTautological
  decide

lemma noTaut179 : Tree.AllNonTautological t179 := by
  change NonTautological t179.conclusion ∧ t0.AllNonTautological ∧ t167.AllNonTautological
  refine ⟨?_, noTaut0, noTaut167⟩
  rw [cert179.2.1]
  unfold NonTautological
  decide

lemma noTaut180 : Tree.AllNonTautological t180 := by
  change NonTautological t180.conclusion ∧ t0.AllNonTautological ∧ t166.AllNonTautological
  refine ⟨?_, noTaut0, noTaut166⟩
  rw [cert180.2.1]
  unfold NonTautological
  decide

lemma noTaut181 : Tree.AllNonTautological t181 := by
  change NonTautological t181.conclusion ∧ t169.AllNonTautological ∧ t168.AllNonTautological
  refine ⟨?_, noTaut169, noTaut168⟩
  rw [cert181.2.1]
  unfold NonTautological
  decide

lemma noTaut182 : Tree.AllNonTautological t182 := by
  change NonTautological t182.conclusion ∧ t165.AllNonTautological ∧ t175.AllNonTautological
  refine ⟨?_, noTaut165, noTaut175⟩
  rw [cert182.2.1]
  unfold NonTautological
  decide

lemma noTaut183 : Tree.AllNonTautological t183 := by
  change NonTautological t183.conclusion ∧ t174.AllNonTautological ∧ t168.AllNonTautological
  refine ⟨?_, noTaut174, noTaut168⟩
  rw [cert183.2.1]
  unfold NonTautological
  decide

lemma noTaut184 : Tree.AllNonTautological t184 := by
  change NonTautological t184.conclusion ∧ t165.AllNonTautological ∧ t173.AllNonTautological
  refine ⟨?_, noTaut165, noTaut173⟩
  rw [cert184.2.1]
  unfold NonTautological
  decide

lemma noTaut185 : Tree.AllNonTautological t185 := by
  change NonTautological t185.conclusion ∧ t172.AllNonTautological ∧ t168.AllNonTautological
  refine ⟨?_, noTaut172, noTaut168⟩
  rw [cert185.2.1]
  unfold NonTautological
  decide

lemma noTaut186 : Tree.AllNonTautological t186 := by
  change NonTautological t186.conclusion ∧ t0.AllNonTautological ∧ t182.AllNonTautological
  refine ⟨?_, noTaut0, noTaut182⟩
  rw [cert186.2.1]
  unfold NonTautological
  decide

lemma noTaut187 : Tree.AllNonTautological t187 := by
  change NonTautological t187.conclusion ∧ t180.AllNonTautological ∧ t183.AllNonTautological
  refine ⟨?_, noTaut180, noTaut183⟩
  rw [cert187.2.1]
  unfold NonTautological
  decide

lemma noTaut188 : Tree.AllNonTautological t188 := by
  change NonTautological t188.conclusion ∧ t179.AllNonTautological ∧ t185.AllNonTautological
  refine ⟨?_, noTaut179, noTaut185⟩
  rw [cert188.2.1]
  unfold NonTautological
  decide

lemma noTaut189 : Tree.AllNonTautological t189 := by
  change NonTautological t189.conclusion ∧ t181.AllNonTautological ∧ t183.AllNonTautological
  refine ⟨?_, noTaut181, noTaut183⟩
  rw [cert189.2.1]
  unfold NonTautological
  decide

lemma noTaut190 : Tree.AllNonTautological t190 := by
  change NonTautological t190.conclusion ∧ t0.AllNonTautological ∧ t177.AllNonTautological
  refine ⟨?_, noTaut0, noTaut177⟩
  rw [cert190.2.1]
  unfold NonTautological
  decide

lemma noTaut191 : Tree.AllNonTautological t191 := by
  change NonTautological t191.conclusion ∧ t179.AllNonTautological ∧ t178.AllNonTautological
  refine ⟨?_, noTaut179, noTaut178⟩
  rw [cert191.2.1]
  unfold NonTautological
  decide

lemma noTaut192 : Tree.AllNonTautological t192 := by
  change NonTautological t192.conclusion ∧ t176.AllNonTautological ∧ t185.AllNonTautological
  refine ⟨?_, noTaut176, noTaut185⟩
  rw [cert192.2.1]
  unfold NonTautological
  decide

lemma noTaut193 : Tree.AllNonTautological t193 := by
  change NonTautological t193.conclusion ∧ t184.AllNonTautological ∧ t178.AllNonTautological
  refine ⟨?_, noTaut184, noTaut178⟩
  rw [cert193.2.1]
  unfold NonTautological
  decide

lemma noTaut194 : Tree.AllNonTautological t194 := by
  change NonTautological t194.conclusion ∧ t176.AllNonTautological ∧ t183.AllNonTautological
  refine ⟨?_, noTaut176, noTaut183⟩
  rw [cert194.2.1]
  unfold NonTautological
  decide

lemma noTaut195 : Tree.AllNonTautological t195 := by
  change NonTautological t195.conclusion ∧ t182.AllNonTautological ∧ t178.AllNonTautological
  refine ⟨?_, noTaut182, noTaut178⟩
  rw [cert195.2.1]
  unfold NonTautological
  decide

lemma noTaut196 : Tree.AllNonTautological t196 := by
  change NonTautological t196.conclusion ∧ t190.AllNonTautological ∧ t193.AllNonTautological
  refine ⟨?_, noTaut190, noTaut193⟩
  rw [cert196.2.1]
  unfold NonTautological
  decide

lemma noTaut197 : Tree.AllNonTautological t197 := by
  change NonTautological t197.conclusion ∧ t191.AllNonTautological ∧ t193.AllNonTautological
  refine ⟨?_, noTaut191, noTaut193⟩
  rw [cert197.2.1]
  unfold NonTautological
  decide

lemma noTaut198 : Tree.AllNonTautological t198 := by
  change NonTautological t198.conclusion ∧ t0.AllNonTautological ∧ t188.AllNonTautological
  refine ⟨?_, noTaut0, noTaut188⟩
  rw [cert198.2.1]
  unfold NonTautological
  decide

lemma noTaut199 : Tree.AllNonTautological t199 := by
  change NonTautological t199.conclusion ∧ t0.AllNonTautological ∧ t187.AllNonTautological
  refine ⟨?_, noTaut0, noTaut187⟩
  rw [cert199.2.1]
  unfold NonTautological
  decide

lemma noTaut200 : Tree.AllNonTautological t200 := by
  change NonTautological t200.conclusion ∧ t186.AllNonTautological ∧ t195.AllNonTautological
  refine ⟨?_, noTaut186, noTaut195⟩
  rw [cert200.2.1]
  unfold NonTautological
  decide

lemma noTaut201 : Tree.AllNonTautological t201 := by
  change NonTautological t201.conclusion ∧ t194.AllNonTautological ∧ t189.AllNonTautological
  refine ⟨?_, noTaut194, noTaut189⟩
  rw [cert201.2.1]
  unfold NonTautological
  decide

lemma noTaut202 : Tree.AllNonTautological t202 := by
  change NonTautological t202.conclusion ∧ t186.AllNonTautological ∧ t193.AllNonTautological
  refine ⟨?_, noTaut186, noTaut193⟩
  rw [cert202.2.1]
  unfold NonTautological
  decide

lemma noTaut203 : Tree.AllNonTautological t203 := by
  change NonTautological t203.conclusion ∧ t192.AllNonTautological ∧ t189.AllNonTautological
  refine ⟨?_, noTaut192, noTaut189⟩
  rw [cert203.2.1]
  unfold NonTautological
  decide

lemma noTaut204 : Tree.AllNonTautological t204 := by
  change NonTautological t204.conclusion ∧ t0.AllNonTautological ∧ t200.AllNonTautological
  refine ⟨?_, noTaut0, noTaut200⟩
  rw [cert204.2.1]
  unfold NonTautological
  decide

lemma noTaut205 : Tree.AllNonTautological t205 := by
  change NonTautological t205.conclusion ∧ t199.AllNonTautological ∧ t201.AllNonTautological
  refine ⟨?_, noTaut199, noTaut201⟩
  rw [cert205.2.1]
  unfold NonTautological
  decide

lemma noTaut206 : Tree.AllNonTautological t206 := by
  change NonTautological t206.conclusion ∧ t198.AllNonTautological ∧ t203.AllNonTautological
  refine ⟨?_, noTaut198, noTaut203⟩
  rw [cert206.2.1]
  unfold NonTautological
  decide

lemma noTaut207 : Tree.AllNonTautological t207 := by
  change NonTautological t207.conclusion ∧ t0.AllNonTautological ∧ t196.AllNonTautological
  refine ⟨?_, noTaut0, noTaut196⟩
  rw [cert207.2.1]
  unfold NonTautological
  decide

lemma noTaut208 : Tree.AllNonTautological t208 := by
  change NonTautological t208.conclusion ∧ t198.AllNonTautological ∧ t197.AllNonTautological
  refine ⟨?_, noTaut198, noTaut197⟩
  rw [cert208.2.1]
  unfold NonTautological
  decide

lemma noTaut209 : Tree.AllNonTautological t209 := by
  change NonTautological t209.conclusion ∧ t202.AllNonTautological ∧ t197.AllNonTautological
  refine ⟨?_, noTaut202, noTaut197⟩
  rw [cert209.2.1]
  unfold NonTautological
  decide

lemma noTaut210 : Tree.AllNonTautological t210 := by
  change NonTautological t210.conclusion ∧ t200.AllNonTautological ∧ t197.AllNonTautological
  refine ⟨?_, noTaut200, noTaut197⟩
  rw [cert210.2.1]
  unfold NonTautological
  decide

lemma noTaut211 : Tree.AllNonTautological t211 := by
  change NonTautological t211.conclusion ∧ t207.AllNonTautological ∧ t209.AllNonTautological
  refine ⟨?_, noTaut207, noTaut209⟩
  rw [cert211.2.1]
  unfold NonTautological
  decide

lemma noTaut212 : Tree.AllNonTautological t212 := by
  change NonTautological t212.conclusion ∧ t208.AllNonTautological ∧ t209.AllNonTautological
  refine ⟨?_, noTaut208, noTaut209⟩
  rw [cert212.2.1]
  unfold NonTautological
  decide

lemma noTaut213 : Tree.AllNonTautological t213 := by
  change NonTautological t213.conclusion ∧ t0.AllNonTautological ∧ t206.AllNonTautological
  refine ⟨?_, noTaut0, noTaut206⟩
  rw [cert213.2.1]
  unfold NonTautological
  decide

lemma noTaut214 : Tree.AllNonTautological t214 := by
  change NonTautological t214.conclusion ∧ t0.AllNonTautological ∧ t205.AllNonTautological
  refine ⟨?_, noTaut0, noTaut205⟩
  rw [cert214.2.1]
  unfold NonTautological
  decide

lemma noTaut215 : Tree.AllNonTautological t215 := by
  change NonTautological t215.conclusion ∧ t204.AllNonTautological ∧ t210.AllNonTautological
  refine ⟨?_, noTaut204, noTaut210⟩
  rw [cert215.2.1]
  unfold NonTautological
  decide

lemma noTaut216 : Tree.AllNonTautological t216 := by
  change NonTautological t216.conclusion ∧ t204.AllNonTautological ∧ t209.AllNonTautological
  refine ⟨?_, noTaut204, noTaut209⟩
  rw [cert216.2.1]
  unfold NonTautological
  decide

lemma noTaut217 : Tree.AllNonTautological t217 := by
  change NonTautological t217.conclusion ∧ t214.AllNonTautological ∧ t216.AllNonTautological
  refine ⟨?_, noTaut214, noTaut216⟩
  rw [cert217.2.1]
  unfold NonTautological
  decide

lemma noTaut218 : Tree.AllNonTautological t218 := by
  change NonTautological t218.conclusion ∧ t0.AllNonTautological ∧ t211.AllNonTautological
  refine ⟨?_, noTaut0, noTaut211⟩
  rw [cert218.2.1]
  unfold NonTautological
  decide

lemma noTaut219 : Tree.AllNonTautological t219 := by
  change NonTautological t219.conclusion ∧ t213.AllNonTautological ∧ t212.AllNonTautological
  refine ⟨?_, noTaut213, noTaut212⟩
  rw [cert219.2.1]
  unfold NonTautological
  decide

lemma noTaut220 : Tree.AllNonTautological t220 := by
  change NonTautological t220.conclusion ∧ t215.AllNonTautological ∧ t212.AllNonTautological
  refine ⟨?_, noTaut215, noTaut212⟩
  rw [cert220.2.1]
  unfold NonTautological
  decide

lemma noTaut221 : Tree.AllNonTautological t221 := by
  change NonTautological t221.conclusion ∧ t218.AllNonTautological ∧ t219.AllNonTautological
  refine ⟨?_, noTaut218, noTaut219⟩
  rw [cert221.2.1]
  unfold NonTautological
  decide

lemma noTaut222 : Tree.AllNonTautological t222 := by
  change NonTautological t222.conclusion ∧ t217.AllNonTautological ∧ t220.AllNonTautological
  refine ⟨?_, noTaut217, noTaut220⟩
  rw [cert222.2.1]
  unfold NonTautological
  decide

lemma noTaut223 : Tree.AllNonTautological t223 := by
  change NonTautological t223.conclusion ∧ t221.AllNonTautological ∧ t222.AllNonTautological
  refine ⟨?_, noTaut221, noTaut222⟩
  rw [cert223.2.1]
  unfold NonTautological
  decide

end FiniteCounterexample
end Kunisky
