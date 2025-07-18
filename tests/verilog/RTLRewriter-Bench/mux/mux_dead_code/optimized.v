module optimized(
    input x,
    input sel,
    input [7:0] a,        // 8-bit input operand A
    input [7:0] b,        // 8-bit input operand B
    output reg [7:0] result  // Output result
);

// Instantiate separate adder and subtractor
wire [7:0] and_result, or_result;

// Instantiate bitwise AND and OR modules
optimized_and_bitwise and_module(
    .a(a),
    .b(b),
    .and_result(and_result)
);

optimized_or_bitwise or_module(
    .a(a),
    .b(b),
    .or_result(or_result)
);

// Control logic to select the operation based on x and sel
always @(*) begin
    if (x) begin
        // And bitwise module
        result = and_result;
    end else begin
        // Or bitwise module
        result = or_result;
    end
end

endmodule

// Module for AND operation
module optimized_and_bitwise(
    input [7:0] a,
    input [7:0] b,
    output [7:0] and_result
);
    assign and_result = a & b;
endmodule

// Module for OR operation
module optimized_or_bitwise(
    input [7:0] a,
    input [7:0] b,
    output [7:0] or_result
);
    assign or_result = a | b;
endmodule
