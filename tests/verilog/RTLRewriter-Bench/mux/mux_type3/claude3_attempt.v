module claude3_attempt(
    input wire sel,
    input wire a,
    output wire y
);
    assign y = sel ? 1 : a;
endmodule
