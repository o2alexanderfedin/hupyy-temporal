; Temporal Reasoning Engine Proof Certificate
; Generated: 2025-09-27T23:56:24.295348
; Query: {'type': 'before', 'A': 't_A3', 'B': 't_B3'}
; Result: True
; Benchmark: interleaved chains with hidden offset

(set-logic ALL)
(set-option :incremental true)
; ---------- declarations ----------
(declare-const t_A1_s Int)
(declare-const t_A1_e Int)
(assert (<= t_A1_s t_A1_e))
(declare-const t_A2_s Int)
(declare-const t_A2_e Int)
(assert (<= t_A2_s t_A2_e))
(declare-const t_A3_s Int)
(declare-const t_A3_e Int)
(assert (<= t_A3_s t_A3_e))
(declare-const t_A4_s Int)
(declare-const t_A4_e Int)
(assert (<= t_A4_s t_A4_e))
(declare-const t_B1_s Int)
(declare-const t_B1_e Int)
(assert (<= t_B1_s t_B1_e))
(declare-const t_B2_s Int)
(declare-const t_B2_e Int)
(assert (<= t_B2_s t_B2_e))
(declare-const t_B3_s Int)
(declare-const t_B3_e Int)
(assert (<= t_B3_s t_B3_e))
(declare-const t_B4_s Int)
(declare-const t_B4_e Int)
(assert (<= t_B4_s t_B4_e))
; ---------- constraints ----------
(assert (< (+ t_A1_e 0) t_A2_s))
(assert (< (+ t_A2_e 0) t_A3_s))
(assert (< (+ t_A3_e 0) t_A4_s))
(assert (< (+ t_B1_e 0) t_B2_s))
(assert (< (+ t_B2_e 0) t_B3_s))
(assert (< (+ t_B3_e 0) t_B4_s))
(assert (< (+ t_A2_e 0) t_B2_s))
(assert (< (+ t_A3_e 0) t_B3_s))
(assert (>= t_B2_s (+ t_A1_e 45)))
; ---------- query (negated) ----------
(push)
(assert (>= t_A3_e t_B3_s))
(check-sat)
(pop)