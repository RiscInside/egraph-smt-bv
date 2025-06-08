; https://github.com/llvm/llvm-project/issues/72512

define i1 @src(i32 %a, i32 %b){
  %add = add i32 %a, 1
  %sub = sub i32 %add, %b
  %cmp1 = icmp eq i32 %sub, 1
  ret i1 %cmp1
}

define i1 @tgt(i32 %a, i32 %b){
  %cmp1 = icmp eq i32 %a, %b
  ret i1 %cmp1
}
