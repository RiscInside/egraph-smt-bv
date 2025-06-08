; https://github.com/llvm/llvm-project/issues/75004, version with select later in the thread

define i1 @src(i32 noundef %bytes, i1 %c, i1 %c1) local_unnamed_addr #0 {
  %cond.not = icmp ne i32 %bytes, 0
  %or.cond = and i1 %cond.not, %c
  %or.cond20 = and i1 %cond.not, %c1
  %not.or.cond = xor i1 %or.cond, true
  %spec.select = select i1 %not.or.cond, i1 %or.cond20, i1 false
  ret i1 %spec.select
}

define i1 @tgt(i32 noundef %bytes, i1 %c, i1 %c1) local_unnamed_addr #0 {
  %cond = icmp eq i32 %bytes, 0
  %brmerge = select i1 %cond, i1 true, i1 %c
  %not.brmerge = xor i1 %brmerge, true
  %spec.select = select i1 %not.brmerge, i1 %c1, i1 false
  ret i1 %spec.select
}
