define i1 @src(i1 %x, i1 %y) {
start:
  %_4 = and i1 %x, %y
  %_3 = xor i1 %_4, true
  tail call void @llvm.assume(i1 %_3)
  %0 = xor i1 %x, %y
  ret i1 %0
}

define i1 @tgt(i1 %x, i1 %y) {
start:
  %_4 = and i1 %x, %y
  %_3 = xor i1 %_4, true
  tail call void @llvm.assume(i1 %_3)
  %0 = or i1 %x, %y
  ret i1 %0
}

declare void @llvm.assume(i1) 
