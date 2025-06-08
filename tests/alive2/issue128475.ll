; https://github.com/llvm/llvm-project/issues/128475

define i32 @src(i32 %x) {
  %18 = add i32 %x, 63
  %19 = and i32 %18, 63
  %20 = xor i32 %19, 63
  ret i32 %20
}

define i32 @tgt(i32 %x) {
  %18 = sub i32 0, %x
  %19 = and i32 %18, 63
  ret i32 %19
}
