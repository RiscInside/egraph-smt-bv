(set-logic QF_UFBV)

; yosys-smt2-stbv
; yosys-smt2-module DataHazard
(define-sort |DataHazard_s| () (_ BitVec 24))
(define-fun |DataHazard_is| ((state |DataHazard_s|)) Bool (= ((_ extract 0 0) state) #b1))
(define-fun |DataHazard#0| ((state |DataHazard_s|)) Bool (= ((_ extract 1 1) state) #b1)) ; \EX_MEM_RegWrite
; yosys-smt2-input EX_MEM_RegWrite 1
; yosys-smt2-witness {"offset": 0, "path": ["\\EX_MEM_RegWrite"], "smtname": "EX_MEM_RegWrite", "smtoffset": 0, "type": "input", "width": 1}
(define-fun |DataHazard_n EX_MEM_RegWrite| ((state |DataHazard_s|)) Bool (|DataHazard#0| state))
(define-fun |DataHazard#1| ((state |DataHazard_s|)) (_ BitVec 5) ((_ extract 6 2) state)) ; \EX_MEM_WriteAddr
; yosys-smt2-input EX_MEM_WriteAddr 5
; yosys-smt2-witness {"offset": 0, "path": ["\\EX_MEM_WriteAddr"], "smtname": "EX_MEM_WriteAddr", "smtoffset": 0, "type": "input", "width": 5}
(define-fun |DataHazard_n EX_MEM_WriteAddr| ((state |DataHazard_s|)) (_ BitVec 5) (|DataHazard#1| state))
(define-fun |DataHazard#2| ((state |DataHazard_s|)) Bool (distinct (|DataHazard#1| state) #b00000)) ; $ne$DataHazard.v:40$5_Y
(define-fun |DataHazard#3| ((state |DataHazard_s|)) Bool (and (or  (|DataHazard#0| state) false) (or  (|DataHazard#2| state) false))) ; $logic_and$DataHazard.v:40$6_Y
(define-fun |DataHazard#4| ((state |DataHazard_s|)) (_ BitVec 5) ((_ extract 11 7) state)) ; \rs
(define-fun |DataHazard#5| ((state |DataHazard_s|)) Bool (= (|DataHazard#1| state) (|DataHazard#4| state))) ; $eq$DataHazard.v:40$7_Y
(define-fun |DataHazard#6| ((state |DataHazard_s|)) Bool (and (or  (|DataHazard#3| state) false) (or  (|DataHazard#5| state) false))) ; $logic_and$DataHazard.v:40$8_Y
(define-fun |DataHazard#7| ((state |DataHazard_s|)) (_ BitVec 2) (ite (|DataHazard#6| state) #b10 #b00)) ; $ternary$DataHazard.v:40$9_Y
(define-fun |DataHazard#8| ((state |DataHazard_s|)) Bool (= ((_ extract 12 12) state) #b1)) ; \ID_EX_RegWrite
(define-fun |DataHazard#9| ((state |DataHazard_s|)) (_ BitVec 5) ((_ extract 17 13) state)) ; \ID_EX_WriteAddr
(define-fun |DataHazard#10| ((state |DataHazard_s|)) Bool (distinct (|DataHazard#9| state) #b00000)) ; $ne$DataHazard.v:39$1_Y
(define-fun |DataHazard#11| ((state |DataHazard_s|)) Bool (and (or  (|DataHazard#8| state) false) (or  (|DataHazard#10| state) false))) ; $logic_and$DataHazard.v:39$2_Y
(define-fun |DataHazard#12| ((state |DataHazard_s|)) Bool (= (|DataHazard#9| state) (|DataHazard#4| state))) ; $eq$DataHazard.v:39$3_Y
(define-fun |DataHazard#13| ((state |DataHazard_s|)) Bool (and (or  (|DataHazard#11| state) false) (or  (|DataHazard#12| state) false))) ; $logic_and$DataHazard.v:39$4_Y
(define-fun |DataHazard#14| ((state |DataHazard_s|)) (_ BitVec 2) (ite (|DataHazard#13| state) #b01 (|DataHazard#7| state))) ; \ForwardA
; yosys-smt2-output ForwardA 2
(define-fun |DataHazard_n ForwardA| ((state |DataHazard_s|)) (_ BitVec 2) (|DataHazard#14| state))
(define-fun |DataHazard#15| ((state |DataHazard_s|)) Bool (distinct (|DataHazard#1| state) #b00000)) ; $ne$DataHazard.v:45$15_Y
(define-fun |DataHazard#16| ((state |DataHazard_s|)) Bool (and (or  (|DataHazard#0| state) false) (or  (|DataHazard#15| state) false))) ; $logic_and$DataHazard.v:45$16_Y
(define-fun |DataHazard#17| ((state |DataHazard_s|)) (_ BitVec 5) ((_ extract 22 18) state)) ; \rt
(define-fun |DataHazard#18| ((state |DataHazard_s|)) Bool (= (|DataHazard#1| state) (|DataHazard#17| state))) ; $eq$DataHazard.v:45$17_Y
(define-fun |DataHazard#19| ((state |DataHazard_s|)) Bool (and (or  (|DataHazard#16| state) false) (or  (|DataHazard#18| state) false))) ; $logic_and$DataHazard.v:45$18_Y
(define-fun |DataHazard#20| ((state |DataHazard_s|)) (_ BitVec 2) (ite (|DataHazard#19| state) #b10 #b00)) ; $ternary$DataHazard.v:45$19_Y
(define-fun |DataHazard#21| ((state |DataHazard_s|)) Bool (distinct (|DataHazard#9| state) #b00000)) ; $ne$DataHazard.v:44$11_Y
(define-fun |DataHazard#22| ((state |DataHazard_s|)) Bool (and (or  (|DataHazard#8| state) false) (or  (|DataHazard#21| state) false))) ; $logic_and$DataHazard.v:44$12_Y
(define-fun |DataHazard#23| ((state |DataHazard_s|)) Bool (= (|DataHazard#9| state) (|DataHazard#17| state))) ; $eq$DataHazard.v:44$13_Y
(define-fun |DataHazard#24| ((state |DataHazard_s|)) Bool (and (or  (|DataHazard#22| state) false) (or  (|DataHazard#23| state) false))) ; $logic_and$DataHazard.v:44$14_Y
(define-fun |DataHazard#25| ((state |DataHazard_s|)) (_ BitVec 2) (ite (|DataHazard#24| state) #b01 (|DataHazard#20| state))) ; \ForwardB
; yosys-smt2-output ForwardB 2
(define-fun |DataHazard_n ForwardB| ((state |DataHazard_s|)) (_ BitVec 2) (|DataHazard#25| state))
(define-fun |DataHazard#26| ((state |DataHazard_s|)) Bool (= ((_ extract 23 23) state) #b1)) ; \ID_EX_MemRead
; yosys-smt2-input ID_EX_MemRead 1
; yosys-smt2-witness {"offset": 0, "path": ["\\ID_EX_MemRead"], "smtname": "ID_EX_MemRead", "smtoffset": 0, "type": "input", "width": 1}
(define-fun |DataHazard_n ID_EX_MemRead| ((state |DataHazard_s|)) Bool (|DataHazard#26| state))
; yosys-smt2-input ID_EX_RegWrite 1
; yosys-smt2-witness {"offset": 0, "path": ["\\ID_EX_RegWrite"], "smtname": "ID_EX_RegWrite", "smtoffset": 0, "type": "input", "width": 1}
(define-fun |DataHazard_n ID_EX_RegWrite| ((state |DataHazard_s|)) Bool (|DataHazard#8| state))
; yosys-smt2-input ID_EX_WriteAddr 5
; yosys-smt2-witness {"offset": 0, "path": ["\\ID_EX_WriteAddr"], "smtname": "ID_EX_WriteAddr", "smtoffset": 0, "type": "input", "width": 5}
(define-fun |DataHazard_n ID_EX_WriteAddr| ((state |DataHazard_s|)) (_ BitVec 5) (|DataHazard#9| state))
(define-fun |DataHazard#27| ((state |DataHazard_s|)) Bool (distinct (|DataHazard#9| state) #b00000)) ; $ne$DataHazard.v:49$21_Y
(define-fun |DataHazard#28| ((state |DataHazard_s|)) Bool (and (or  (|DataHazard#26| state) false) (or  (|DataHazard#27| state) false))) ; $logic_and$DataHazard.v:49$22_Y
(define-fun |DataHazard#29| ((state |DataHazard_s|)) Bool (= (|DataHazard#9| state) (|DataHazard#4| state))) ; $eq$DataHazard.v:49$23_Y
(define-fun |DataHazard#30| ((state |DataHazard_s|)) Bool (= (|DataHazard#9| state) (|DataHazard#17| state))) ; $eq$DataHazard.v:49$24_Y
(define-fun |DataHazard#31| ((state |DataHazard_s|)) Bool (or  (|DataHazard#29| state) false  (|DataHazard#30| state) false)) ; $logic_or$DataHazard.v:49$25_Y
(define-fun |DataHazard#32| ((state |DataHazard_s|)) Bool (and (or  (|DataHazard#28| state) false) (or  (|DataHazard#31| state) false))) ; \LW_Stall
; yosys-smt2-output LW_Stall 1
(define-fun |DataHazard_n LW_Stall| ((state |DataHazard_s|)) Bool (|DataHazard#32| state))
; yosys-smt2-input rs 5
; yosys-smt2-witness {"offset": 0, "path": ["\\rs"], "smtname": "rs", "smtoffset": 0, "type": "input", "width": 5}
(define-fun |DataHazard_n rs| ((state |DataHazard_s|)) (_ BitVec 5) (|DataHazard#4| state))
; yosys-smt2-input rt 5
; yosys-smt2-witness {"offset": 0, "path": ["\\rt"], "smtname": "rt", "smtoffset": 0, "type": "input", "width": 5}
(define-fun |DataHazard_n rt| ((state |DataHazard_s|)) (_ BitVec 5) (|DataHazard#17| state))
(define-fun |DataHazard_a| ((state |DataHazard_s|)) Bool true)
(define-fun |DataHazard_u| ((state |DataHazard_s|)) Bool true)
(define-fun |DataHazard_i| ((state |DataHazard_s|)) Bool true)
(define-fun |DataHazard_h| ((state |DataHazard_s|)) Bool true)
(define-fun |DataHazard_t| ((state |DataHazard_s|) (next_state |DataHazard_s|)) Bool true) ; end of module DataHazard
; yosys-smt2-module DataHazard_raw
(define-sort |DataHazard_raw_s| () (_ BitVec 24))
(define-fun |DataHazard_raw_is| ((state |DataHazard_raw_s|)) Bool (= ((_ extract 0 0) state) #b1))
(define-fun |DataHazard_raw#0| ((state |DataHazard_raw_s|)) Bool (= ((_ extract 1 1) state) #b1)) ; \EX_MEM_RegWrite
; yosys-smt2-input EX_MEM_RegWrite 1
; yosys-smt2-witness {"offset": 0, "path": ["\\EX_MEM_RegWrite"], "smtname": "EX_MEM_RegWrite", "smtoffset": 0, "type": "input", "width": 1}
(define-fun |DataHazard_raw_n EX_MEM_RegWrite| ((state |DataHazard_raw_s|)) Bool (|DataHazard_raw#0| state))
(define-fun |DataHazard_raw#1| ((state |DataHazard_raw_s|)) (_ BitVec 5) ((_ extract 6 2) state)) ; \EX_MEM_WriteAddr
; yosys-smt2-input EX_MEM_WriteAddr 5
; yosys-smt2-witness {"offset": 0, "path": ["\\EX_MEM_WriteAddr"], "smtname": "EX_MEM_WriteAddr", "smtoffset": 0, "type": "input", "width": 5}
(define-fun |DataHazard_raw_n EX_MEM_WriteAddr| ((state |DataHazard_raw_s|)) (_ BitVec 5) (|DataHazard_raw#1| state))
(define-fun |DataHazard_raw#2| ((state |DataHazard_raw_s|)) (_ BitVec 5) ((_ extract 11 7) state)) ; \rs
(define-fun |DataHazard_raw#3| ((state |DataHazard_raw_s|)) Bool (= (|DataHazard_raw#1| state) (|DataHazard_raw#2| state))) ; $eq$DataHazardRaw.v:36$34_Y
(define-fun |DataHazard_raw#4| ((state |DataHazard_raw_s|)) (_ BitVec 9) (ite (|DataHazard_raw#3| state) #b000000010 #b000000000)) ; $procmux$56_Y
(define-fun |DataHazard_raw#5| ((state |DataHazard_raw_s|)) Bool (distinct (|DataHazard_raw#1| state) #b00000)) ; $ne$DataHazardRaw.v:35$32_Y
(define-fun |DataHazard_raw#6| ((state |DataHazard_raw_s|)) Bool (and (or  (|DataHazard_raw#0| state) false) (or  (|DataHazard_raw#5| state) false))) ; $logic_and$DataHazardRaw.v:35$33_Y
(define-fun |DataHazard_raw#7| ((state |DataHazard_raw_s|)) (_ BitVec 9) (ite (|DataHazard_raw#6| state) (|DataHazard_raw#4| state) #b000000000)) ; $procmux$58_Y
(define-fun |DataHazard_raw#8| ((state |DataHazard_raw_s|)) Bool (= ((_ extract 12 12) state) #b1)) ; \ID_EX_RegWrite
(define-fun |DataHazard_raw#9| ((state |DataHazard_raw_s|)) (_ BitVec 5) ((_ extract 17 13) state)) ; \ID_EX_WriteAddr
(define-fun |DataHazard_raw#10| ((state |DataHazard_raw_s|)) Bool (distinct (|DataHazard_raw#9| state) #b00000)) ; $ne$DataHazardRaw.v:28$28_Y
(define-fun |DataHazard_raw#11| ((state |DataHazard_raw_s|)) Bool (and (or  (|DataHazard_raw#8| state) false) (or  (|DataHazard_raw#10| state) false))) ; $logic_and$DataHazardRaw.v:28$29_Y
(define-fun |DataHazard_raw#12| ((state |DataHazard_raw_s|)) (_ BitVec 9) (ite (|DataHazard_raw#11| state) #b000000000 (|DataHazard_raw#7| state))) ; $procmux$61_Y
(define-fun |DataHazard_raw#13| ((state |DataHazard_raw_s|)) (_ BitVec 9) (ite (|DataHazard_raw#6| state) (|DataHazard_raw#12| state) #b000000000)) ; $procmux$70_Y
(define-fun |DataHazard_raw#14| ((state |DataHazard_raw_s|)) (_ BitVec 9) (ite (|DataHazard_raw#11| state) #b000000000 (|DataHazard_raw#13| state))) ; $procmux$73_Y
(define-fun |DataHazard_raw#15| ((state |DataHazard_raw_s|)) Bool (= (|DataHazard_raw#9| state) (|DataHazard_raw#2| state))) ; $eq$DataHazardRaw.v:29$30_Y
(define-fun |DataHazard_raw#16| ((state |DataHazard_raw_s|)) (_ BitVec 9) (ite (|DataHazard_raw#15| state) #b000000001 #b000000000)) ; $procmux$83_Y
(define-fun |DataHazard_raw#17| ((state |DataHazard_raw_s|)) (_ BitVec 9) (ite (|DataHazard_raw#11| state) (|DataHazard_raw#16| state) #b000000000)) ; $procmux$85_Y
(define-fun |DataHazard_raw#18| ((state |DataHazard_raw_s|)) (_ BitVec 9) (ite (|DataHazard_raw#11| state) (|DataHazard_raw#17| state) (|DataHazard_raw#14| state))) ; $procmux$91_Y
; yosys-smt2-output ForwardA 2
(define-fun |DataHazard_raw_n ForwardA| ((state |DataHazard_raw_s|)) (_ BitVec 2) ((_ extract 1 0) (|DataHazard_raw#18| state)))
(define-fun |DataHazard_raw#19| ((state |DataHazard_raw_s|)) (_ BitVec 5) ((_ extract 22 18) state)) ; \rt
(define-fun |DataHazard_raw#20| ((state |DataHazard_raw_s|)) Bool (= (|DataHazard_raw#1| state) (|DataHazard_raw#19| state))) ; $eq$DataHazardRaw.v:38$35_Y
(define-fun |DataHazard_raw#21| ((state |DataHazard_raw_s|)) (_ BitVec 9) (ite (|DataHazard_raw#20| state) #b000000010 #b000000000)) ; $procmux$47_Y
(define-fun |DataHazard_raw#22| ((state |DataHazard_raw_s|)) (_ BitVec 9) (ite (|DataHazard_raw#6| state) (|DataHazard_raw#21| state) #b000000000)) ; $procmux$49_Y
(define-fun |DataHazard_raw#23| ((state |DataHazard_raw_s|)) (_ BitVec 9) (ite (|DataHazard_raw#11| state) #b000000000 (|DataHazard_raw#22| state))) ; $procmux$52_Y
(define-fun |DataHazard_raw#24| ((state |DataHazard_raw_s|)) (_ BitVec 9) (ite (|DataHazard_raw#6| state) (|DataHazard_raw#23| state) #b000000000)) ; $procmux$64_Y
(define-fun |DataHazard_raw#25| ((state |DataHazard_raw_s|)) (_ BitVec 9) (ite (|DataHazard_raw#11| state) #b000000000 (|DataHazard_raw#24| state))) ; $procmux$67_Y
(define-fun |DataHazard_raw#26| ((state |DataHazard_raw_s|)) Bool (= (|DataHazard_raw#9| state) (|DataHazard_raw#19| state))) ; $eq$DataHazardRaw.v:31$31_Y
(define-fun |DataHazard_raw#27| ((state |DataHazard_raw_s|)) (_ BitVec 9) (ite (|DataHazard_raw#26| state) #b000000001 #b000000000)) ; $procmux$77_Y
(define-fun |DataHazard_raw#28| ((state |DataHazard_raw_s|)) (_ BitVec 9) (ite (|DataHazard_raw#11| state) (|DataHazard_raw#27| state) #b000000000)) ; $procmux$79_Y
(define-fun |DataHazard_raw#29| ((state |DataHazard_raw_s|)) (_ BitVec 9) (ite (|DataHazard_raw#11| state) (|DataHazard_raw#28| state) (|DataHazard_raw#25| state))) ; $procmux$88_Y
; yosys-smt2-output ForwardB 2
(define-fun |DataHazard_raw_n ForwardB| ((state |DataHazard_raw_s|)) (_ BitVec 2) ((_ extract 1 0) (|DataHazard_raw#29| state)))
(define-fun |DataHazard_raw#30| ((state |DataHazard_raw_s|)) Bool (= ((_ extract 23 23) state) #b1)) ; \ID_EX_MemRead
; yosys-smt2-input ID_EX_MemRead 1
; yosys-smt2-witness {"offset": 0, "path": ["\\ID_EX_MemRead"], "smtname": "ID_EX_MemRead", "smtoffset": 0, "type": "input", "width": 1}
(define-fun |DataHazard_raw_n ID_EX_MemRead| ((state |DataHazard_raw_s|)) Bool (|DataHazard_raw#30| state))
; yosys-smt2-input ID_EX_RegWrite 1
; yosys-smt2-witness {"offset": 0, "path": ["\\ID_EX_RegWrite"], "smtname": "ID_EX_RegWrite", "smtoffset": 0, "type": "input", "width": 1}
(define-fun |DataHazard_raw_n ID_EX_RegWrite| ((state |DataHazard_raw_s|)) Bool (|DataHazard_raw#8| state))
; yosys-smt2-input ID_EX_WriteAddr 5
; yosys-smt2-witness {"offset": 0, "path": ["\\ID_EX_WriteAddr"], "smtname": "ID_EX_WriteAddr", "smtoffset": 0, "type": "input", "width": 5}
(define-fun |DataHazard_raw_n ID_EX_WriteAddr| ((state |DataHazard_raw_s|)) (_ BitVec 5) (|DataHazard_raw#9| state))
(define-fun |DataHazard_raw#31| ((state |DataHazard_raw_s|)) Bool (distinct (|DataHazard_raw#9| state) #b00000)) ; $ne$DataHazardRaw.v:43$36_Y
(define-fun |DataHazard_raw#32| ((state |DataHazard_raw_s|)) Bool (and (or  (|DataHazard_raw#30| state) false) (or  (|DataHazard_raw#31| state) false))) ; $logic_and$DataHazardRaw.v:43$37_Y
(define-fun |DataHazard_raw#33| ((state |DataHazard_raw_s|)) Bool (= (|DataHazard_raw#9| state) (|DataHazard_raw#2| state))) ; $eq$DataHazardRaw.v:43$38_Y
(define-fun |DataHazard_raw#34| ((state |DataHazard_raw_s|)) Bool (= (|DataHazard_raw#9| state) (|DataHazard_raw#19| state))) ; $eq$DataHazardRaw.v:43$39_Y
(define-fun |DataHazard_raw#35| ((state |DataHazard_raw_s|)) Bool (or  (|DataHazard_raw#33| state) false  (|DataHazard_raw#34| state) false)) ; $logic_or$DataHazardRaw.v:43$40_Y
(define-fun |DataHazard_raw#36| ((state |DataHazard_raw_s|)) Bool (and (or  (|DataHazard_raw#32| state) false) (or  (|DataHazard_raw#35| state) false))) ; $logic_and$DataHazardRaw.v:43$41_Y
(define-fun |DataHazard_raw#37| ((state |DataHazard_raw_s|)) (_ BitVec 9) (ite (|DataHazard_raw#36| state) #b000000001 #b000000000)) ; $procmux$43_Y
; yosys-smt2-output LW_Stall 1
(define-fun |DataHazard_raw_n LW_Stall| ((state |DataHazard_raw_s|)) Bool (= ((_ extract 0 0) (|DataHazard_raw#37| state)) #b1))
; yosys-smt2-input rs 5
; yosys-smt2-witness {"offset": 0, "path": ["\\rs"], "smtname": "rs", "smtoffset": 0, "type": "input", "width": 5}
(define-fun |DataHazard_raw_n rs| ((state |DataHazard_raw_s|)) (_ BitVec 5) (|DataHazard_raw#2| state))
; yosys-smt2-input rt 5
; yosys-smt2-witness {"offset": 0, "path": ["\\rt"], "smtname": "rt", "smtoffset": 0, "type": "input", "width": 5}
(define-fun |DataHazard_raw_n rt| ((state |DataHazard_raw_s|)) (_ BitVec 5) (|DataHazard_raw#19| state))
(define-fun |DataHazard_raw_a| ((state |DataHazard_raw_s|)) Bool true)
(define-fun |DataHazard_raw_u| ((state |DataHazard_raw_s|)) Bool true)
(define-fun |DataHazard_raw_i| ((state |DataHazard_raw_s|)) Bool true)
(define-fun |DataHazard_raw_h| ((state |DataHazard_raw_s|)) Bool true)
(define-fun |DataHazard_raw_t| ((state |DataHazard_raw_s|) (next_state |DataHazard_raw_s|)) Bool true) ; end of module DataHazard_raw
; yosys-smt2-module miter
(define-sort |miter_s| () (_ BitVec 82))
(define-fun |miter_is| ((state |miter_s|)) Bool (= ((_ extract 0 0) state) #b1))
; yosys-smt2-cell DataHazard gold
; yosys-smt2-witness {"path": ["\\gold"], "smtname": "gold", "type": "cell"}
(define-fun |miter#0| ((state |miter_s|)) Bool (= ((_ extract 1 1) state) #b1)) ; \gold_LW_Stall
(define-fun |miter#1| ((state |miter_s|)) (_ BitVec 2) ((_ extract 3 2) state)) ; \gold_ForwardB
(define-fun |miter#2| ((state |miter_s|)) (_ BitVec 2) ((_ extract 5 4) state)) ; \gold_ForwardA
(define-fun |miter_h gold| ((state |miter_s|)) (_ BitVec 24) ((_ extract 29 6) state))
; yosys-smt2-cell DataHazard_raw gate
; yosys-smt2-witness {"path": ["\\gate"], "smtname": "gate", "type": "cell"}
(define-fun |miter#3| ((state |miter_s|)) Bool (= ((_ extract 30 30) state) #b1)) ; \gate_LW_Stall
(define-fun |miter#4| ((state |miter_s|)) (_ BitVec 2) ((_ extract 32 31) state)) ; \gate_ForwardB
(define-fun |miter#5| ((state |miter_s|)) (_ BitVec 2) ((_ extract 34 33) state)) ; \gate_ForwardA
(define-fun |miter_h gate| ((state |miter_s|)) (_ BitVec 24) ((_ extract 58 35) state))
(define-fun |miter#6| ((state |miter_s|)) Bool (= (|miter#2| state) (|miter#5| state))) ; $auto$miter.cc:242:create_miter_equiv$94
(define-fun |miter#7| ((state |miter_s|)) Bool (= (|miter#1| state) (|miter#4| state))) ; $auto$miter.cc:242:create_miter_equiv$96
(define-fun |miter#8| ((state |miter_s|)) Bool (= (ite (|miter#0| state) #b1 #b0) (ite (|miter#3| state) #b1 #b0))) ; $auto$miter.cc:242:create_miter_equiv$98
(define-fun |miter#9| ((state |miter_s|)) Bool (and  (|miter#6| state) (|miter#7| state) (|miter#8| state))) ; $auto$miter.cc:269:create_miter_equiv$100
(define-fun |miter#10| ((state |miter_s|)) (_ BitVec 1) (bvnot (ite (|miter#9| state) #b1 #b0))) ; \trigger
; yosys-smt2-output trigger 1
(define-fun |miter_n trigger| ((state |miter_s|)) Bool (= ((_ extract 0 0) (|miter#10| state)) #b1))
(define-fun |miter#11| ((state |miter_s|)) (_ BitVec 5) ((_ extract 63 59) state)) ; \in_rt
; yosys-smt2-input in_rt 5
; yosys-smt2-witness {"offset": 0, "path": ["\\in_rt"], "smtname": "in_rt", "smtoffset": 0, "type": "input", "width": 5}
(define-fun |miter_n in_rt| ((state |miter_s|)) (_ BitVec 5) (|miter#11| state))
(define-fun |miter#12| ((state |miter_s|)) (_ BitVec 5) ((_ extract 68 64) state)) ; \in_rs
; yosys-smt2-input in_rs 5
; yosys-smt2-witness {"offset": 0, "path": ["\\in_rs"], "smtname": "in_rs", "smtoffset": 0, "type": "input", "width": 5}
(define-fun |miter_n in_rs| ((state |miter_s|)) (_ BitVec 5) (|miter#12| state))
(define-fun |miter#13| ((state |miter_s|)) (_ BitVec 5) ((_ extract 73 69) state)) ; \in_ID_EX_WriteAddr
; yosys-smt2-input in_ID_EX_WriteAddr 5
; yosys-smt2-witness {"offset": 0, "path": ["\\in_ID_EX_WriteAddr"], "smtname": "in_ID_EX_WriteAddr", "smtoffset": 0, "type": "input", "width": 5}
(define-fun |miter_n in_ID_EX_WriteAddr| ((state |miter_s|)) (_ BitVec 5) (|miter#13| state))
(define-fun |miter#14| ((state |miter_s|)) Bool (= ((_ extract 74 74) state) #b1)) ; \in_ID_EX_RegWrite
; yosys-smt2-input in_ID_EX_RegWrite 1
; yosys-smt2-witness {"offset": 0, "path": ["\\in_ID_EX_RegWrite"], "smtname": "in_ID_EX_RegWrite", "smtoffset": 0, "type": "input", "width": 1}
(define-fun |miter_n in_ID_EX_RegWrite| ((state |miter_s|)) Bool (|miter#14| state))
(define-fun |miter#15| ((state |miter_s|)) Bool (= ((_ extract 75 75) state) #b1)) ; \in_ID_EX_MemRead
; yosys-smt2-input in_ID_EX_MemRead 1
; yosys-smt2-witness {"offset": 0, "path": ["\\in_ID_EX_MemRead"], "smtname": "in_ID_EX_MemRead", "smtoffset": 0, "type": "input", "width": 1}
(define-fun |miter_n in_ID_EX_MemRead| ((state |miter_s|)) Bool (|miter#15| state))
(define-fun |miter#16| ((state |miter_s|)) (_ BitVec 5) ((_ extract 80 76) state)) ; \in_EX_MEM_WriteAddr
; yosys-smt2-input in_EX_MEM_WriteAddr 5
; yosys-smt2-witness {"offset": 0, "path": ["\\in_EX_MEM_WriteAddr"], "smtname": "in_EX_MEM_WriteAddr", "smtoffset": 0, "type": "input", "width": 5}
(define-fun |miter_n in_EX_MEM_WriteAddr| ((state |miter_s|)) (_ BitVec 5) (|miter#16| state))
(define-fun |miter#17| ((state |miter_s|)) Bool (= ((_ extract 81 81) state) #b1)) ; \in_EX_MEM_RegWrite
; yosys-smt2-input in_EX_MEM_RegWrite 1
; yosys-smt2-witness {"offset": 0, "path": ["\\in_EX_MEM_RegWrite"], "smtname": "in_EX_MEM_RegWrite", "smtoffset": 0, "type": "input", "width": 1}
(define-fun |miter_n in_EX_MEM_RegWrite| ((state |miter_s|)) Bool (|miter#17| state))
; yosys-smt2-assert 0 $auto$miter.cc:274:create_miter_equiv$101
(define-fun |miter_a 0| ((state |miter_s|)) Bool (or (|miter#9| state) (not true))) ; $auto$miter.cc:274:create_miter_equiv$101
(define-fun |miter_a| ((state |miter_s|)) Bool (and
  (|miter_a 0| state)
  (|DataHazard_raw_a| (|miter_h gate| state))
  (|DataHazard_a| (|miter_h gold| state))
))
(define-fun |miter_u| ((state |miter_s|)) Bool (and
  (|DataHazard_raw_u| (|miter_h gate| state))
  (|DataHazard_u| (|miter_h gold| state))
))
(define-fun |miter_i| ((state |miter_s|)) Bool (and
  (|DataHazard_raw_i| (|miter_h gate| state))
  (|DataHazard_i| (|miter_h gold| state))
))
(define-fun |miter_h| ((state |miter_s|)) Bool (and
  (= (|miter_is| state) (|DataHazard_raw_is| (|miter_h gate| state)))
  (= (|miter#11| state) (|DataHazard_raw_n rt| (|miter_h gate| state))) ; DataHazard_raw.rt
  (= (|miter#12| state) (|DataHazard_raw_n rs| (|miter_h gate| state))) ; DataHazard_raw.rs
  (= (|miter#3| state) (|DataHazard_raw_n LW_Stall| (|miter_h gate| state))) ; DataHazard_raw.LW_Stall
  (= (|miter#13| state) (|DataHazard_raw_n ID_EX_WriteAddr| (|miter_h gate| state))) ; DataHazard_raw.ID_EX_WriteAddr
  (= (|miter#14| state) (|DataHazard_raw_n ID_EX_RegWrite| (|miter_h gate| state))) ; DataHazard_raw.ID_EX_RegWrite
  (= (|miter#15| state) (|DataHazard_raw_n ID_EX_MemRead| (|miter_h gate| state))) ; DataHazard_raw.ID_EX_MemRead
  (= (|miter#4| state) (|DataHazard_raw_n ForwardB| (|miter_h gate| state))) ; DataHazard_raw.ForwardB
  (= (|miter#5| state) (|DataHazard_raw_n ForwardA| (|miter_h gate| state))) ; DataHazard_raw.ForwardA
  (= (|miter#16| state) (|DataHazard_raw_n EX_MEM_WriteAddr| (|miter_h gate| state))) ; DataHazard_raw.EX_MEM_WriteAddr
  (= (|miter#17| state) (|DataHazard_raw_n EX_MEM_RegWrite| (|miter_h gate| state))) ; DataHazard_raw.EX_MEM_RegWrite
  (= (|miter_is| state) (|DataHazard_is| (|miter_h gold| state)))
  (= (|miter#11| state) (|DataHazard_n rt| (|miter_h gold| state))) ; DataHazard.rt
  (= (|miter#12| state) (|DataHazard_n rs| (|miter_h gold| state))) ; DataHazard.rs
  (= (|miter#0| state) (|DataHazard_n LW_Stall| (|miter_h gold| state))) ; DataHazard.LW_Stall
  (= (|miter#13| state) (|DataHazard_n ID_EX_WriteAddr| (|miter_h gold| state))) ; DataHazard.ID_EX_WriteAddr
  (= (|miter#14| state) (|DataHazard_n ID_EX_RegWrite| (|miter_h gold| state))) ; DataHazard.ID_EX_RegWrite
  (= (|miter#15| state) (|DataHazard_n ID_EX_MemRead| (|miter_h gold| state))) ; DataHazard.ID_EX_MemRead
  (= (|miter#1| state) (|DataHazard_n ForwardB| (|miter_h gold| state))) ; DataHazard.ForwardB
  (= (|miter#2| state) (|DataHazard_n ForwardA| (|miter_h gold| state))) ; DataHazard.ForwardA
  (= (|miter#16| state) (|DataHazard_n EX_MEM_WriteAddr| (|miter_h gold| state))) ; DataHazard.EX_MEM_WriteAddr
  (= (|miter#17| state) (|DataHazard_n EX_MEM_RegWrite| (|miter_h gold| state))) ; DataHazard.EX_MEM_RegWrite
  (|DataHazard_raw_h| (|miter_h gate| state))
  (|DataHazard_h| (|miter_h gold| state))
))
(define-fun |miter_t| ((state |miter_s|) (next_state |miter_s|)) Bool (and
  (|DataHazard_raw_t| (|miter_h gate| state) (|miter_h gate| next_state))
  (|DataHazard_t| (|miter_h gold| state) (|miter_h gold| next_state))
)) ; end of module miter
; end of yosys output

(declare-const state |miter_s|)
(assert (|miter_h| state)) ; Hierarchy assertion
(assert (not (|miter_a| state))) ; Miter assertion failure - output of miter is true
(check-sat)
