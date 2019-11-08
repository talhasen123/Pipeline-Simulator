`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 14.04.2019 17:15:39
// Design Name: 
// Module Name: pipelineTestbench
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


module pipelineTestbench();
    
    logic clk, reset, memtoreg, zero, alusrc, regdst, regwrite, jump, PCSrcM, branch, memwrite, StallF, StallD;
    logic [31:0] instr, aluout, WriteDataM;
    
    always 
    begin
       clk = 1; #5; clk = 0; #5;
    end
    
    top dut( clk, reset, memtoreg, zero, alusrc, regdst, regwrite, jump, PCSrcM, branch, memwrite, StallF, StallD, instr, aluout, WriteDataM);
    
    initial begin
    reset = 1; #1; reset = 0; #1; 
    end
endmodule
