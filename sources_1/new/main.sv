`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: Alper Karadag, Ziya Erkoc
// 
// Create Date: 03.12.2018 19:22:49
// Design Name: 
// Module Name: pipes
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

// Define pipes that exist in the PipelinedDatapath. 
// The pipe between Writeback (W) and Fetch (F), as well as Fetch (F) and Decode (D) is given to you.
// Create the rest of the pipes where inputs follow the naming conventions in the book.
module main(input   logic 	 clk, reset, switchInput,         
	     output  logic memtoreg, zero, alusrc, regdst, regwrite, jump, PCSrcM, branch, memwrite,
	     output  logic [3:0] an,
	     output  logic [6:0] c,
	     output  logic dp);
	     
	     logic clk_pulse, StallF, StallD;
         logic[31:0] writedata, dataadr, pc, instr;
         
         top top(clk_pulse,reset, memtoreg, zero, alusrc, regdst, regwrite, jump, PCSrcM, branch, memwrite, StallF, StallD, instr, dataadr, writedata); 
         display_controller display_controller (clk, reset, 4'b1111, writedata[7:4], writedata[3:0], dataadr[7:4], dataadr[3:0], an, c, dp);
         pulse_controller pulse_controller (clk, switchInput, reset, clk_pulse);
    
endmodule

module top(input logic clk, reset, 
           output logic memtoreg, zero, alusrc, regdst, regwrite, jump, PCSrcM, branch, memwrite, StallF, StallD,
           output logic [31:0] instr, aluout, WriteDataM);
    
    logic [31:0] PCF, resultW, instrOut;
    
    mips mips(clk, reset, PCF, instr, aluout, resultW, instrOut, WriteDataM,  memtoreg, zero, alusrc, regdst, regwrite, jump, PCSrcM, branch, memwrite, StallF, StallD);
    imem imem(PCF[7:2], instr);
endmodule

module PipeFtoD(input logic[31:0] instr, PcPlus4F,
                input logic EN, FlushD, clk, reset,		// StallD will be connected as this EN
                output logic[31:0] instrD, PcPlus4D);
    
    always_ff @(posedge clk, posedge reset)begin
        if (reset)begin
            instrD <= 0;
            PcPlus4D <= 0;
        end
        else if(~EN)
            begin
            instrD<=instr;
            PcPlus4D<=PcPlus4F;
            end
        else if (FlushD)
            begin
            instrD <= 0;
            PcPlus4D <= PcPlus4D;
            end
        else begin
            instrD <= instrD;
            PcPlus4D <= PcPlus4D;
        end
    end
endmodule

// Similarly, the pipe between Writeback (W) and Fetch (F) is given as follows.

module PipeWtoF(input logic[31:0] PC,
                input logic EN, clk, reset,		// StallF will be connected as this EN
                output logic[31:0] PCF);
    
    always_ff @(posedge clk, posedge reset)begin
        if (reset)
            PCF <= 0;
        else if(~EN)
            begin
            PCF<=PC;
            end
        else 
            PCF <= PCF;
    end
endmodule

// *******************************************************************************
// Below, you are given the argument lists of the modules PipeDtoE, PipeEtoM, PipeMtoW.
// You should implement them by looking at pipelined processor image given to you.   
// Don't forget that these codes are tested but you can always make changes if you want.
// Note that some output logics there for debugging purposes, in other words to trace their values in simulation.
// *******************************************************************************


module PipeDtoE(input logic clr, clk, reset, RegWriteD, MemtoRegD, MemWriteD,
                input logic[2:0] AluControlD,
                input logic AluSrcD, RegDstD, BranchD,
                input logic[31:0] RD1D, RD2D,
                input logic[4:0] RsD, RtD, RdD,
                input logic[31:0] SignImmD,
                input logic[31:0] PCPlus4D,
                    output logic RegWriteE, MemtoRegE, MemWriteE,
                    output logic[2:0] AluControlE,
                    output logic AluSrcE, RegDstE, BranchE,
                    output logic[31:0] RD1E, RD2E,
                    output logic[4:0] RsE, RtE, RdE,
                    output logic[31:0] SignImmE,
                    output logic[31:0] PCPlus4E);

    always_ff @(posedge clk, posedge reset)begin
        // ******************************************************************************
        // YOUR CODE HERE
        if ( reset)
            begin
            RegWriteE <= 0;
            MemtoRegE <= 0;
            MemWriteE <= 0;
            AluControlE <= 0;
            AluSrcE <= 0;
            RegDstE <= 0;
            BranchE <= 0;
            RD1E <= 0;
            RD2E <= 0;
            RsE <= 0;
            RtE <= 0;
            RdE <= 0;
            SignImmE <= 0;
            PCPlus4E <= 0;
            end
        else if  ( clr)
            begin
            RsE <= 0;
            RtE <= 0;
            RdE <= 0;
            RegWriteE <= 0;
            MemWriteE <= 0;
            BranchE <= 0;
            end
        else
            begin
            RD1E <= RD1D;
            RD2E <= RD2D;
            RsE <= RsD;
            RtE <= RtD;
            RdE <= RdD;
            SignImmE <= SignImmD;
            PCPlus4E <= PCPlus4D;
            RegWriteE <= RegWriteD;
            MemtoRegE <= MemtoRegD;
            MemWriteE <= MemWriteD;
            AluControlE <= AluControlD;
            AluSrcE <= AluSrcD;
            RegDstE <= RegDstD;
            BranchE <= BranchD;
            end
        // ******************************************************************************
    end
endmodule

module PipeEtoM(input logic clk, reset, RegWriteE, MemtoRegE, MemWriteE, BranchE, Zero,
                input logic[31:0] ALUOut,
                input logic [31:0] WriteDataE,
                input logic[4:0] WriteRegE,
                input logic[31:0] PCBranchE,
                    output logic RegWriteM, MemtoRegM, MemWriteM, BranchM, ZeroM,
                    output logic[31:0] ALUOutM,
                    output logic [31:0] WriteDataM,
                    output logic[4:0] WriteRegM,
                    output logic[31:0] PCBranchM);
    
    always_ff @(posedge clk, posedge reset) begin
        // ******************************************************************************
        // YOUR CODE HERE
        if ( reset) begin
           RegWriteM <= 0;
           MemtoRegM <= 0;
           MemWriteM <= 0;
           BranchM <= 0;
           ZeroM <= 0;
           ALUOutM <= 0;
           WriteDataM <= 0;
           WriteRegM <= 0;
           PCBranchM <= 0;
        end
        else begin
           ALUOutM <= ALUOut;
           WriteDataM <= WriteDataE;
           WriteRegM <= WriteRegE;
           PCBranchM <= PCBranchE; 
           RegWriteM <= RegWriteE;
           MemtoRegM <= MemtoRegE;
           MemWriteM <= MemWriteE;
           BranchM <= BranchE;
           ZeroM <= Zero;
        end
        // ******************************************************************************
    end
endmodule

module PipeMtoW(input logic clk, reset, RegWriteM, MemtoRegM,
                input logic[31:0] ReadDataM, ALUOutM,
                input logic[4:0] WriteRegM,
                    output logic RegWriteW, MemtoRegW,
                    output logic[31:0] ReadDataW, ALUOutW,
                    output logic[4:0] WriteRegW);

		always_ff @(posedge clk, posedge reset) begin
            // ******************************************************************************
		    // YOUR CODE HERE
		    if ( reset)
		      begin
		      ReadDataW <= 0;
		      ALUOutW <= 0;
		      WriteRegW <= 0;
		      RegWriteW <= 0;
		      MemtoRegW <= 0;
		      end
		    else begin
		      ReadDataW <= ReadDataM;
		      ALUOutW <= ALUOutM;
		      WriteRegW <= WriteRegM;
		      RegWriteW <= RegWriteM;
		      MemtoRegW <= MemtoRegM;		      
		      end		    
            // ******************************************************************************
        end
endmodule



// *******************************************************************************
// End of the individual pipe definitions.
// ******************************************************************************

// *******************************************************************************
// Below is the definition of the datapath.
// The signature of the module is given. The datapath will include (not limited to) the following items:
//  (1) Adder that adds 4 to PC
//  (2) Shifter that shifts SignImmE to left by 2
//  (3) Sign extender and Register file
//  (4) PipeFtoD
//  (5) PipeDtoE and ALU
//  (5) Adder for PCBranchM
//  (6) PipeEtoM and Data Memory
//  (7) PipeMtoW
//  (8) Many muxes
//  (9) Hazard unit
//  ...?
// *******************************************************************************

module datapath (input  logic clk, reset,
		         input logic [31:0] PCF, instr,	
		         input logic RegWriteD, MemtoRegD, MemWriteD, //RegWriteW,
		         //input logic [4:0] WriteRegW,
		         input logic [2:0] ALUControlD,
		         input logic AluSrcD, RegDstD, BranchD,
		             output logic PCSrcM, Zero, StallF, StallD,
		             output logic[31:0] PCBranchM, PCPlus4F, PCPlus4D, instrD, ALUOut, ResultW, WriteDataM, RD1D, RD2D); 

	// ********************************************************************
	// Here, define the wires (logics) that are needed inside this pipelined datapath module
    // You are given the wires connecting the Hazard Unit.
    // Notice that StallD and StallF are given as output for debugging
	// ********************************************************************

	// Add necessary wires (logics).
	logic FlushE, FlushD, RegWriteE, MemtoRegE, MemWriteE, AluSrcE, RegDstE, BranchE, RegWriteM, MemtoRegM, MemWriteM, BranchM, ZeroM;
	logic MemtoRegW, RegWriteW;// StallF, StallD;
    logic [1:0] ForwardAE, ForwardBE; 
    logic [2:0] AluControlE;       
    logic [4:0] RsD, RtD, RdD, RsE, RtE, RdE, WriteRegE, WriteRegM, WriteRegW;
    logic [31:0] PCPlus4E, PCBranchE, SignImmE, SignImmESh, SignImmD, SrcAE, SrcBE, RD1E, RD2E, WriteDataE, ALUOutM, ReadDataW, ALUOutW, ReadDataM;

	// ********************************************************************
	// Instantiate the required modules below in the order of the datapath flow.
	// ********************************************************************
	assign PCSrcM = BranchM & ZeroM;// YOUR CODE HERE
	assign RsD = instrD[25:21];// YOUR CODE HERE
    assign RtD = instrD[20:16];// YOUR CODE HERE
    assign RdD = instrD[15:11];// YOUR CODE HERE
    
	// Below, PipeFtoD and regfile instantiations are given
    // Add other instantiations
    // BE CAREFUL ABOUT THE ORDER OF PARAMETERS!
	adder       pcadd1(PCF, 32'b100, PCPlus4F);
    sl2         immsh(SignImmE , SignImmESh);
    signext     se(instrD[15:0], SignImmD);
    
	PipeFtoD ftd(instr, PCPlus4F, StallD, FlushD, clk, reset, instrD, PCPlus4D); 
	PipeDtoE dte(FlushE, clk, reset, RegWriteD, MemtoRegD, MemWriteD,
                     ALUControlD,
                     AluSrcD, RegDstD, BranchD,
                     RD1D, RD2D,
                     RsD, RtD, RdD,
                     SignImmD,
                     PCPlus4D,
                     RegWriteE, MemtoRegE, MemWriteE,
                     AluControlE,
                     AluSrcE, RegDstE, BranchE,
                     RD1E, RD2E,
                     RsE, RtE, RdE,
                     SignImmE,
                     PCPlus4E);
                     
    alu        alu( SrcAE, SrcBE, AluControlE, ALUOut, Zero);
    
    adder      pcbranchadd( SignImmESh, PCPlus4E, PCBranchE);
    
	PipeEtoM etm(clk, reset, RegWriteE, MemtoRegE, MemWriteE, BranchE, Zero,
                     ALUOut,
                     WriteDataE,
                     WriteRegE,
                     PCBranchE,
                     RegWriteM, MemtoRegM, MemWriteM, BranchM, ZeroM,
                     ALUOutM,
                     WriteDataM,
                     WriteRegM,
                     PCBranchM);
                     
    dmem     dmem(clk, MemWriteM, ALUOutM, WriteDataM, ReadDataM); 
     
	PipeMtoW mtw(clk, reset, RegWriteM, MemtoRegM,
                     ReadDataM, ALUOutM,
                     WriteRegM,
                     RegWriteW, MemtoRegW,
                     ReadDataW, ALUOutW,
                     WriteRegW);
	     
	regfile rf (clk, RegWriteW, instrD[25:21], instrD[20:16],
            WriteRegW, ResultW, RD1D, RD2D);                                
	
    mux4 #(32) SrcAEmux(RD1E, ResultW, ALUOutM, 32'b0, ForwardAE, SrcAE);
    mux4 #(32) writedatamux(RD2E, ResultW, ALUOutM, 32'b0, ForwardBE, WriteDataE); 
    mux2 #(32) SrcBEmux( WriteDataE, SignImmE, AluSrcE, SrcBE);
    mux2 #(32) resmux(ALUOutW, ReadDataW, MemtoRegW, ResultW);
    mux2 #(5)  dstmux(RtE, RdE, RegDstE, WriteRegE);
	
    HazardUnit hzu(RegWriteW, WriteRegW, RegWriteM, MemtoRegM, WriteRegM, RegWriteE, MemtoRegE, BranchD, BranchE, RsE, RtE, RsD, RtD, ForwardAE, ForwardBE, FlushE, FlushD, StallD, StallF);
endmodule



// Hazard Unit with inputs and outputs named
// according to the convention that is followed on the book.
module HazardUnit( input logic RegWriteW,
                input logic [4:0] WriteRegW,
                input logic RegWriteM,MemToRegM,
                input logic [4:0] WriteRegM,
                input logic RegWriteE,MemtoRegE,
                input logic BranchD, BranchE,
                input logic [4:0] rsE,rtE,
                input logic [4:0] rsD,rtD,
                output logic [1:0] ForwardAE, ForwardBE,
                output logic FlushE, FlushD, StallD, StallF);
   
    logic lwstall;
    always_comb begin
        
        // ********************************************************************
        // Here, write equations for the Hazard Logic.
        // If you have troubles, please study pages ~420-430 in your book.
        // ********************************************************************
        if (((rsD == rtE) | (rtD == rtE)) & MemtoRegE) lwstall <= 1;
        else lwstall <= 0; 
        //assign lwstall = ((rsD == rtE) | (rtD == rtE)) & MemtoRegE;
        FlushE <= lwstall;
        FlushD <= BranchD;
        StallD <= BranchE | lwstall;
        StallF <= BranchE | BranchD | lwstall;
        if ( (rsE != 0) & (rsE == WriteRegM) & RegWriteM)
            ForwardAE <= 2'b10;
        else if ( (rsE != 0) & (rsE == WriteRegW) & RegWriteW)
            ForwardAE <= 2'b01;
        else
            ForwardAE <= 2'b00;
            
        if ( (rtE != 0) & (rtE == WriteRegM) & RegWriteM)
            ForwardBE <= 2'b10;
        else if ( (rtE != 0) & (rtE == WriteRegW) & RegWriteW)
            ForwardBE <= 2'b01;
        else
            ForwardBE <= 2'b00;
    end

endmodule


module mips (input  logic        clk, reset,
             output logic[31:0]  PCF,
             input  logic[31:0]  instr,
             output logic[31:0]  aluout, resultW,
             output logic[31:0]  instrOut, WriteDataM,
             output logic memtoreg, zero, alusrc, regdst, regwrite, jump, PCSrcM, branch, memwrite, StallF, StallD);

    // ********************************************************************
    // You can change the logics below but if you didn't change the signitures of 
    // above modules you will need these.
    // ********************************************************************

  //  logic memtoreg, zero, alusrc, regdst, regwrite, jump, PCSrcM, branch, memwrite; //regwriteW;
    logic [31:0] PCPlus4F, PCPlus4D, PCm, PCBranchM, instrD, RD1D, RD2D;
    logic [2:0] alucontrol;
    logic [1:0] ForwardAE, ForwardBE;
    //logic StallF, StallD;
    //logic [4:0] WriteRegW;
    assign instrOut = instr;
    
	// ********************************************************************
	// Below, instantiate a controller and a datapath with their new (if modified) 
	// signatures and corresponding connections.
    // Also, you might want to instantiate PipeWtoF and pcsrcmux here.
    // Note that this is not the only solution.
    // You can do it in your way as long as it works.
	// ********************************************************************
	controller cl(instrD[31:26], instrD[5:0], memtoreg, memwrite, alusrc, regdst, regwrite, jump, alucontrol, branch);
	datapath dp(clk, reset, PCF, instr, regwrite, memtoreg, memwrite, alucontrol, alusrc, regdst, branch, 
	            PCSrcM, zero, StallF, StallD, PCBranchM, PCPlus4F, PCPlus4D, instrD, aluout, resultW, WriteDataM, RD1D, RD2D);
	PipeWtoF pipeWF(PCm, StallF, clk, reset, PCF);
	mux2 #(32) pcsrcmux(PCPlus4F, PCBranchM, PCSrcM, PCm);

endmodule


// External instruction memory used by MIPS single-cycle
// processor. It models instruction memory as a stored-program 
// ROM, with address as input, and instruction as output
// Modify it to test your own programs.

module imem ( input logic [5:0] addr, output logic [31:0] instr);

// imem is modeled as a lookup table, a stored-program byte-addressable ROM
	always_comb
	   case ({addr,2'b00})		   	// word-aligned fetch
//
// 	***************************************************************************
//	Here, you should paste the test cases that are given to you in lab document.
//  You can write your own test cases and try it as well.
//	Below is the program from the single-cycle lab.
//	***************************************************************************
//
//		address		instruction
//		-------		-----------
		8'h00:      instr = 32'h20080007;
        8'h04:      instr = 32'h20090005;
        8'h08:      instr = 32'h200a0000;
        8'h0c:      instr = 32'h210b000f;
        8'h10:      instr = 32'h01095020;
        8'h14:      instr = 32'h01095025;
        8'h18:      instr = 32'h01095024;
        8'h1c:      instr = 32'h01095022;
        8'h20:      instr = 32'h0109502a;
        8'h24:      instr = 32'had280002;
        8'h28:      instr = 32'h8d090000;
        8'h2c:      instr = 32'h1100fff5;
        8'h30:      instr = 32'h200a000a;
        8'h34:      instr = 32'h2009000c;
       	8'h38:      instr = 32'h20080005;
        8'h3c:      instr = 32'h21090006;
        8'h40:      instr = 32'h01285020;
        8'h44:      instr = 32'h20080005;
        8'h48:      instr = 32'h20090006;
        8'h4c:      instr = 32'h20040001;
        8'h50:      instr = 32'h20050002;
        8'h54:      instr = 32'had280000;
        8'h58:      instr = 32'h8d090001;
        8'h5c:      instr = 32'h01245020;
        8'h60:      instr = 32'h01255022;
        8'h64:      instr = 32'h20090002;
        8'h68:      instr = 32'h10000002;
        8'h6c:      instr = 32'h20090005;
        8'h70:      instr = 32'h21290006;
        8'h74:      instr = 32'h20090008;
        8'h78:      instr = 32'h20040000;
        8'h7c:      instr = 32'h20050000;
        8'h80:      instr = 32'hac090000;

	     default:  instr = {32{1'bx}};	// unknown address
	   endcase
endmodule


// 	***************************************************************************
//	Below are the modules that you shouldn't need to modify at all..
//	***************************************************************************

module controller(input  logic[5:0] op, funct,
                  output logic     memtoreg, memwrite,
                  output logic     alusrc,
                  output logic     regdst, regwrite,
                  output logic     jump,
                  output logic[2:0] alucontrol,
                  output logic branch);

   logic [1:0] aluop;

   maindec md (op, memtoreg, memwrite, branch, alusrc, regdst, regwrite, 
         jump, aluop);

   aludec  ad (funct, aluop, alucontrol);

endmodule

// External data memory used by MIPS single-cycle processor

module dmem (input  logic        clk, we,
             input  logic[31:0]  a, wd,
             output logic[31:0]  rd);

   logic  [31:0] RAM[63:0];
  
   assign rd = RAM[a[31:2]];    // word-aligned  read (for lw)

   always_ff @(posedge clk)
     if (we)
       RAM[a[31:2]] <= wd;      // word-aligned write (for sw)

endmodule

module maindec (input logic[5:0] op, 
	              output logic memtoreg, memwrite, branch,
	              output logic alusrc, regdst, regwrite, jump,
	              output logic[1:0] aluop );
   logic [8:0] controls;

   assign {regwrite, regdst, alusrc, branch, memwrite,
                memtoreg,  aluop, jump} = controls;

  always_comb
    case(op)
      6'b000000: controls <= 9'b110000100; // R-type
      6'b100011: controls <= 9'b101001000; // LW
      6'b101011: controls <= 9'b001010000; // SW
      6'b000100: controls <= 9'b000100010; // BEQ
      6'b001000: controls <= 9'b101000000; // ADDI
      6'b000010: controls <= 9'b000000001; // J
      default:   controls <= 9'bxxxxxxxxx; // illegal op
    endcase
endmodule

module aludec (input    logic[5:0] funct,
               input    logic[1:0] aluop,
               output   logic[2:0] alucontrol);
  always_comb
    case(aluop)
      2'b00: alucontrol  = 3'b010;  // add  (for lw/sw/addi)
      2'b01: alucontrol  = 3'b110;  // sub   (for beq)
      default: case(funct)          // R-TYPE instructions
          6'b100000: alucontrol  = 3'b010; // ADD
          6'b100010: alucontrol  = 3'b110; // SUB
          6'b100100: alucontrol  = 3'b000; // AND
          6'b100101: alucontrol  = 3'b001; // OR
          6'b101010: alucontrol  = 3'b111; // SLT
          default:   alucontrol  = 3'bxxx; // ???
        endcase
    endcase
endmodule

module regfile (input    logic clk, we3, 
                input    logic[4:0]  ra1, ra2, wa3, 
                input    logic[31:0] wd3, 
                output   logic[31:0] rd1, rd2);

  logic [31:0] rf [31:0];

  // three ported register file: read two ports combinationally
  // write third port on rising edge of clock. Register0 hardwired to 0.

  always_ff @(negedge clk)
     if (we3) 
         rf [wa3] <= wd3;	

  assign rd1 = (ra1 != 0) ? rf [ra1] : 0;
  assign rd2 = (ra2 != 0) ? rf[ ra2] : 0;

endmodule

module alu(input  logic [31:0] a, b, 
           input  logic [2:0]  alucont, 
           output logic [31:0] result,
           output logic zero, input logic reset);

    always_comb begin
        case(alucont)
            3'b010: result = a + b;
            3'b110: result = a - b;
            3'b000: result = a & b;
            3'b001: result = a | b;
            3'b111: result = (a < b) ? 1 : 0;
            default: result = {32{1'bx}};
        endcase
        if(reset)
            result <= 0;
        end
    
    assign zero = (result == 0) ? 1'b1 : 1'b0;
    
endmodule

module adder (input  logic[31:0] a, b,
              output logic[31:0] y);
     
     assign y = a + b;
endmodule

module sl2 (input  logic[31:0] a,
            output logic[31:0] y);
     
     assign y = {a[29:0], 2'b00}; // shifts left by 2
endmodule

module signext (input  logic[15:0] a,
                output logic[31:0] y);
              
  assign y = {{16{a[15]}}, a};    // sign-extends 16-bit a
endmodule

// parameterized register
module flopr #(parameter WIDTH = 8)
              (input logic clk, reset, 
	       input logic[WIDTH-1:0] d, 
               output logic[WIDTH-1:0] q);

  always_ff@(posedge clk, posedge reset)
    if (reset) q <= 0; 
    else       q <= d;
endmodule


// paramaterized 2-to-1 MUX
module mux2 #(parameter WIDTH = 8)
             (input  logic[WIDTH-1:0] d0, d1,  
              input  logic s, 
              output logic[WIDTH-1:0] y);
  
   assign y = s ? d1 : d0; 
endmodule

// paramaterized 4-to-1 MUX
module mux4 #(parameter WIDTH = 8)
             (input  logic[WIDTH-1:0] d0, d1, d2, d3,  
              input  logic[1:0] s, 
              output logic[WIDTH-1:0] y);
  
   assign y = s[1] ? (s[0] ? d3 : d2) : (s[0] ? d1 : d0); 
endmodule