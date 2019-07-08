`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 03.12.2018 01:33:28
// Design Name: 
// Module Name: testbench
// Project Name: 
// Target Devices: 
// Tool Versions: 
// Description: 
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////


module testbench();

    logic clk, reset, memwrite_out, branch, stallF, stallD, FlushE, FlushM;
    
    logic  [31:0] pc_out, readdata_out, writedata_out, instr_out, alu_out;

    top main(clk, reset, stallF, stallD, FlushE, FlushM, pc_out, memwrite_out, branch, readdata_out, writedata_out, instr_out, alu_out);

    initial begin
             clk = 0;
             forever #50 clk = ~clk;
    end 

     initial begin
            reset <= 1; #50;
            reset <= 0; #50;
            
       end

endmodule