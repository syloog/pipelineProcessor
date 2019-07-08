// Define pipes that exist in the PipelinedDatapath. 
// The pipe between Writeback (W) and Fetch (F), as well as Fetch (F) and Decode (D) is given to you.
// Create the rest of the pipes where inputs follow the naming conventions in the book.


module PipeFtoD(
input logic [31:0] instrF, pcPlusF,
input logic EN, clk, reset,		// StallD will be connected as this EN
output logic [31:0] instrD, pcPlusD);

                always_ff @(posedge clk, posedge reset)
                    if (reset)
                         begin
                         instrD <= 0;
                         pcPlusD <= 0;
                         end
                    else if (EN)
                        begin
                        instrD <= instrF;
                        pcPlusD <= pcPlusF;
                        end

endmodule

// Similarly, the pipe between Writeback (W) and Fetch (F) is given as follows.

module PipeWtoF(
input logic[31:0] PC,
input logic EN, clk, reset,		// StallF will be connected as this EN
output logic[31:0] PCF);

                always_ff @(posedge clk, posedge reset)
                    	if (reset)
                    	    begin
				            PCF <= 0;
				            end
			    else if (EN)
                        	begin
                        	PCF<=PC;
                       	 	end
endmodule

module PipeDtoE(
input logic [31:0] pcPlus4D, rdD1, rdD2,
input logic [4:0] rsD, rtD, rdD, 
input logic RegWriteD, MemtoRegD, MemWriteD, 
input logic [2:0] ALUControlD, 
input logic ALUSrcD, RegDstD, BranchD, 
input logic [31:0] immD, 
input logic clk, FlushE, 
output logic RegWriteE, MemtoRegE, MemWriteE, 
output logic [2:0] ALUControlE, 
output logic ALUSrcE, RegDstE, BranchE, 
output logic [31:0] rdE1, rdE2, 
output logic [4:0] rsE, rtE, rdE, 
output logic [31:0] immE, 
output logic [31:0] pcPlus4E);

		always_ff @(posedge clk)
             if(FlushE)
                
                begin
                RegWriteE <= 0;
				MemtoRegE <= 0;
				MemWriteE <= 0;
                ALUControlE <= 0;
				ALUSrcE <= 0;
				RegDstE <= 0;
                BranchE <= 0;
				rdE1 <= 0;
				rdE2 <= 0;
                rsE <= 0;
				rtE <= 0;
				rdE <= 0;
                immE <= 0;
				pcPlus4E <= 0;
                end
                
			else
				
				begin
				RegWriteE <= RegWriteD;
				MemtoRegE <= MemtoRegD;
				MemWriteE <= MemWriteD;
                ALUControlE <= ALUControlD;
				ALUSrcE <= ALUSrcD;
				RegDstE <= RegDstD;
                BranchE <= BranchD;
				rdE1 <= rdD1;
				rdE2 <= rdD2;
                rsE <= rsD;
				rtE <= rtD;
				rdE <= rdD;
                immE <= immD;
				pcPlus4E <= pcPlus4D;
				end
				
endmodule

module PipeEtoM(
input logic RegWriteE, MemtoRegE, MemWriteE, BranchE, zeroE, 
input logic [31:0] ALUOutE, WriteDataE, 
input logic [4:0] WriteRegE, 
input logic [31:0] PCBranchE, 
input logic clk, 
input logic FlushM,
output logic RegWriteM, MemtoRegM, MemWriteM, BranchM, zeroM, 
output logic [31:0] ALUOutM, WriteDataM, 
output logic [4:0] WriteRegM, 
output logic [31:0] PCBranchM);
		
		always_ff @(posedge clk)
		    if(FlushM)                
                        begin
                            RegWriteM <= 0;
                            MemtoRegM <= 0;
                            MemWriteM <= 0;
                            BranchM <= 0;
                            zeroM <= 0;
                            ALUOutM <= 0;
                            WriteDataM <= 0;
                            WriteRegM <= 0;
                            PCBranchM <= 0;
                        end
            else
                        begin
                            RegWriteM <= RegWriteE;
                            MemtoRegM <= MemtoRegE;
                            MemWriteM <= MemWriteE;
                            BranchM <= BranchE;
                            zeroM <= zeroE;
                            ALUOutM <= ALUOutE;
                            WriteDataM <= WriteDataE;
                            WriteRegM <= WriteRegE;
                            PCBranchM <= PCBranchE;
                        end
endmodule

module PipeMtoW(
input logic RegWriteM, MemtoRegM, 
input logic [31:0] readDataM, ALUOutM, 
input logic [4:0] WriteRegM, 
input logic clk, 
output logic RegWriteW, MemtoRegW, 
output logic [31:0] readDataW, ALUOutW, 
output logic [4:0] WriteRegW);

		always_ff @(posedge clk)
			begin
				RegWriteW <= RegWriteM;
				MemtoRegW <= MemtoRegM;
				readDataW <= readDataM;
				ALUOutW <= ALUOutM;
				WriteRegW <= WriteRegM;
			end
endmodule

module top (input  logic clk, reset,
             output logic stallF, stallD, FlushE, FlushM,
             output logic [31:0]  pc_outF,
             output logic  memwrite_outM, branch_outD,
             output logic [31:0] readdata_outM, writedata_outM, instr_outF, alu_outM);

  wire [31:0] pc, instr, aluResult, writedata, readdata;
  
  logic memwrite, branch;

  mips mips1 (clk, reset, stallF, stallD, FlushE, FlushM, pc, instr, aluResult, memwrite, branch, readdata, writedata);

  imem code (pc[7:2], instr);
    
  dmem data (clk, memwrite, aluResult, writedata, readdata);

  assign pc_outF = pc;
  assign instr_outF = instr;
  assign readdata_outM = readdata;
  assign writedata_outM = writedata;
  assign memwrite_outM = memwrite;
  assign branch_outD = branch;
  assign alu_outM = aluResult;
  
endmodule

module mips (
input  logic clk, reset,
output logic stallF, stallD, FlushE, FlushM,
output logic [31:0] pc,
input logic [31:0] instr,
output logic [31:0] alu_out,
output logic  memwrite_out, branch_out,
input logic [31:0] readdata_in,
output logic[31:0] writedata_out
);

  logic memtoreg, memwrite, alusrc, regdst, regwrite, jump, branch;
  logic [2:0]  alucontrol;
  logic [5:0] opD, functD;

  controller c (opD, functD, memtoreg, memwrite,
                      alusrc, regdst, regwrite, jump, alucontrol, branch);

  datapath dp (clk, reset, regwrite, memtoreg, memwrite, alucontrol, alusrc, regdst, branch, jump, stallF, stallD, FlushE, FlushM, pc,
                      alu_out, writedata_out, memwrite_out, opD, functD, readdata_in, instr);

    assign branch_out = branch;

endmodule

module datapath (
input logic clk, reset, 
input logic RegWriteD, MemtoRegD, MemWriteD,
input logic [2:0]  ALUControlD,
input logic ALUSrcD, RegDstD, BranchD, jumpD,
output logic stallF, stallD, FlushE, FlushM,
output logic [31:0] pcF,
output logic [31:0] ALUOutM, WriteDataM,
output logic MemWriteM,
output logic [5:0] opD, functD,
input logic [31:0] readDataM,
input logic [31:0] instrF
);

	logic RegWriteW, RegWriteE, MemtoRegE, MemWriteE, ALUSrcE, RegDstE, BranchE, zeroE, zeroM, MemtoRegM, BranchM, pcSrcM, MemtoRegW;

	logic [31:0]  immD, immE, immEShift, ResultW, rdD1, rdD2, rdE1, rdE2, pcPlus4E, SrcAE, WriteDataE, SrcBE, PCBranchE, ALUOutE, PCBranchM, readDataW, ALUOutW, pcnextbr;

    wire [31:0] pcPlus4F, pcPlus4D, pcJumpCheck;

    wire [31:0] instrD;

	logic [1:0] ForwardAE, ForwardBE;

	logic [2:0] ALUControlE;

	logic [4:0] WriteRegW, rsE, rtE, rdE, rsD, rtD, rdD, WriteRegE, WriteRegM;
	
    // Fetch

    adder pcPlus4 (pcF, 32'b100, pcPlus4F); // Adder for next PC

    PipeFtoD pipe1 (instrF, pcPlus4F, ~stallD, clk, reset, instrD, pcPlus4D); // FETCH PIPE
	// Decode

    assign rsD = instrD [25:21]; // Register Source Address
    assign rtD = instrD [20:16]; // Register Target Address
    assign rdD = instrD [15:11]; // Register Destination Address
    assign opD = instrD [31:26]; // OP Field of the Decode Instructýon
    assign functD = instrD [5:0]; // Funct Field of the Decode Instruction
    

	regfile rf (clk, RegWriteW, rsD, rtD, WriteRegW,			
                   ResultW, rdD1, rdD2); // REGISTER FILE
	
	signext signAdd (instrD[15:0], immD); // SIGN EXTENDER

	PipeDtoE pipe2 (pcPlus4D, rdD1, rdD2, rsD, rtD, rdD, RegWriteD, MemtoRegD, MemWriteD, ALUControlD, ALUSrcD, RegDstD, BranchD, immD, clk, FlushE, RegWriteE, MemtoRegE, MemWriteE, ALUControlE, ALUSrcE, RegDstE, BranchE, rdE1, rdE2, rsE, rtE, rdE, immE, pcPlus4E); // DECODE PIPE

	// Execute

	mux3 #(32) muks1 (rdE1, ResultW, ALUOutM, ForwardAE, SrcAE); // SOURCE A CHECKING CONSECUTIVE INSTRUCTIONS' REGISTERS

	mux3 #(32) muks2 (rdE2, ResultW, ALUOutM, ForwardBE, WriteDataE); // SOURCE B CHECKING CONSECUTIVE INSTRUCTIONS' REGISTERS

	mux2 #(32) muks3 (WriteDataE, immE, ALUSrcE, SrcBE); // SOURCE B MUX CONTINUING

	mux2 #(5) muks4 (rtE, rdE, RegDstE, WriteRegE); // WRITE ADDRESS CHECKING CONSECUTIVE INSTRUCTIONS' REGISTERS

	sl2  immsh(immE, immEShift); // IMMEDIATE SHIFTER

	adder pcadd2 (pcPlus4E, immEShift, PCBranchE); // BRANCH PC VALUE

	alu aluDesign (SrcAE, SrcBE, ALUControlE, ALUOutE, zeroE); // ALU

	PipeEtoM pipe3 (RegWriteE, MemtoRegE, MemWriteE, BranchE, zeroE, ALUOutE, WriteDataE, WriteRegE, PCBranchE, clk, FlushM, RegWriteM, MemtoRegM, MemWriteM, BranchM, zeroM, ALUOutM, WriteDataM, WriteRegM, PCBranchM); // EXECUTE PIPE

	// Memory
	
	assign pcSrcM = BranchM & zeroM; // BRANCH ASSIGN

	PipeMtoW pipe4 (RegWriteM, MemtoRegM, readDataM, ALUOutM, WriteRegM, clk, RegWriteW, MemtoRegW, readDataW, ALUOutW, WriteRegW); // MEMORY PIPE
	
	// WriteBack

	mux2 #(32) muks5 (ALUOutW, readDataW, MemtoRegW, ResultW); // RESULT MUX
	
	mux2 #(32) muks6 (pcPlus4F, PCBranchM, pcSrcM, pcnextbr); // PCNEXT MUX

    mux2 #(32) muks7 (pcnextbr, {pcPlus4D[31:28], instrD[25:0], 2'b00}, jumpD, pcJumpCheck); // JUMP MUX

	PipeWtoF pipe5 (pcJumpCheck, ~stallF, clk, reset, pcF); // WRITEBACK PIPE

	// Hazard Unit
	
	HazardUnit unit (pcSrcM, jumpD, RegWriteW, WriteRegW, RegWriteM, MemtoRegM, WriteRegM, RegWriteE, MemtoRegE,
	                           rsE, rtE, instrD[25:21], instrD[20:16], ForwardAE, ForwardBE, FlushE, FlushM, stallD, stallF); // HAZARD UNIT

endmodule


// Hazard Unit with inputs and outputs named
// according to the convention that is followed on the book.

module HazardUnit(
input logic pcSrcM, jumpD, RegWriteW,
input logic [4:0] WriteRegW,
input logic RegWriteM,MemToRegM,
input logic [4:0] WriteRegM,
input logic RegWriteE,MemToRegE,
input logic [4:0] rsE,rtE,
input logic [4:0] rsD,rtD,
output logic [1:0] ForwardAE,ForwardBE,
output logic FlushE,FlushM, StallD,StallF
    );
    
	   logic lwstall;

    	always_comb begin
	    
		lwstall = (((rsD == rtE) | (rtD == rtE)) & MemToRegE) | pcSrcM;
		FlushM = lwstall;
		FlushE = lwstall;
		StallD = lwstall  |  jumpD;
		StallF = lwstall;

		if((rsE != 0) & (rsE == WriteRegM) & RegWriteM)
			ForwardAE = 10;
		else if ((rsE != 0) & (rsE == WriteRegW) & RegWriteW)
			ForwardAE = 01;
		else
			ForwardAE = 00;

		if((rtE != 0) & (rtE == WriteRegM) & RegWriteM)
			ForwardBE = 10;
		else if ((rtE != 0) & (rtE == WriteRegW) & RegWriteW)
			ForwardBE = 01;
		else
			ForwardBE = 00;
    	end
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
//	Here, you can paste your own test cases that you prepared for the part 1-g.
//	Below is a program from the single-cycle lab.
//	***************************************************************************
//
//		address		instruction
//		-------		-----------
		8'h00: instr = 32'h20020005;  	// disassemble, by hand 
		8'h04: instr = 32'h2003000c;  	// or with a program,
		8'h08: instr = 32'h2067fff7;  	// to find out what
		8'h0c: instr = 32'h00e22025;  	// this program does!
		8'h10: instr = 32'h00642824;
		8'h14: instr = 32'h00a42820;
		8'h18: instr = 32'h10a7000a;
		8'h1c: instr = 32'h0064202a;
		8'h20: instr = 32'h10800001;
		8'h24: instr = 32'h20050000;
		8'h28: instr = 32'h00e2202a;
		8'h2c: instr = 32'h00853820;
		8'h30: instr = 32'h00e23822;
		8'h34: instr = 32'hac670044;
		8'h38: instr = 32'h8c020050;
		8'h3c: instr = 32'h08000011;
		8'h40: instr = 32'h20020001;
		8'h44: instr = 32'hac020054;
		8'h48: instr = 32'h08000012;	// j 48, so it will loop here
		8'h4c: instr = 32'h00a42820;
		8'h50: instr = 32'h20020005;
		8'h54: instr = 32'h2003000c;
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
           output logic zero);
    
    always_comb
        case(alucont)
            3'b010: result = a + b;
            3'b110: result = a - b;
            3'b000: result = a & b;
            3'b001: result = a | b;
            3'b111: result = (a < b) ? 1 : 0;
            default: result = {32{1'bx}};
        endcase
    
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


// paramaterized 2-to-1 MUX
module mux2 #(parameter WIDTH = 8)
             (input  logic[WIDTH-1:0] d0, d1,  
              input  logic s, 
              output logic[WIDTH-1:0] y);
  
   assign y = s ? d1 : d0; 
endmodule

module mux3 #(parameter WIDTH = 32)
             (input  logic[WIDTH-1:0] d0, d1, d2,  
              input  logic [1:0] s, 
              output logic[WIDTH-1:0] y);
  
   assign y = s[1] ? d2 : ( s[0] ? d1 : d0);
endmodule