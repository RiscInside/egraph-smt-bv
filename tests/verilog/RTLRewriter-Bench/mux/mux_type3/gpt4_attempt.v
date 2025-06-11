module gpt4_attempt(
    input wire sel,
    input wire a,
    output wire y
);
    // Directly implement the multiplexer logic using a conditional operator
    assign y = sel ? 1'b1 : a;
endmodule
