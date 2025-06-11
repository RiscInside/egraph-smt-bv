module ours(
    input wire sel,
    input wire a,
    output wire y
);
    // Directly implementing the multiplexer logic
    assign y = sel ? 1 : a;
endmodule
