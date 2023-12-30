
module top(input logic clk, reset,
			  output logic [31:0] WriteData, DataAdr,
			  output logic MemWrite);
	
	logic [31:0] PC, ReadData;
	
	//instantiate processor and memory module
	riscvmulti rvmulti(clk, reset, PC, MemWrite, DataAdr,
							 WriteData, ReadData);
	
	id_mem idmem(clk, MemWrite, DataAdr, WriteData, ReadData);
endmodule

module riscvmulti(input  logic        clk, reset,
                   output logic [31:0] PC,
                   output logic        MemWrite,
                   output logic [31:0] DataAdr, WriteData,
                   input  logic [31:0] ReadData);
  
  logic [31:0] Instr;
  logic       RegWrite, Zero, IRWrite, PCWrite, AdrSrc;
  logic [1:0] ResultSrc, ImmSrc, ALUSrcA, ALUSrcB;
  logic [2:0] ALUControl;
  
  controller c(clk, reset, Instr[6:0], Instr[14:12], Instr[30], Zero, ImmSrc, ALUSrcA, ALUSrcB, ResultSrc, AdrSrc, ALUControl, IRWrite, PCWrite, RegWrite, MemWrite);
  
  datapath dp(clk, reset, ResultSrc, PCWrite, AdrSrc, IRWrite,
              ALUSrcA, ALUSrcB, RegWrite,
              ImmSrc, ALUControl,
              Zero, PC, Instr,
              DataAdr, WriteData, ReadData);
endmodule

module datapath(input logic		   clk, reset,
					 input logic  [1:0]  ResultSrc,
					 input logic 		   PCWrite, AdrSrc, IRWrite,
					 input logic  [1:0]  ALUSrcA, ALUSrcB,
					 input logic		   RegWrite,
					 input logic  [1:0]  ImmSrc,
					 input logic  [2:0]  ALUControl,
					 output logic		   Zero, 
					 output logic [31:0] PC,
					 output logic [31:0]	Instr,
					 output logic [31:0]	DataAdr, WriteData,
					 input  logic [31:0] ReadData);


	logic [31:0] PCNext, OldPC;
	logic [31:0] ImmExt;
	logic [31:0] RD1, RD2, A, SrcA, SrcB;
	logic [31:0] Result;
	logic [31:0] ALUOut;
	logic [31:0] Data;
	logic [31:0] ALUResult;
	
	//next PC logic
	assign PCNext = Result;
	//may want to change param PCNext to Result
	flopr #(32) pcreg(clk, reset, /*enable*/ PCWrite, PCNext, PC);
	
	mux2 #(32)	adrmux(PC, Result, AdrSrc, DataAdr);
		
	//2 input register for old PC and Instr from memory
	flopr2 #(32) oldpcreg(clk, reset, IRWrite, PC, ReadData, OldPC, Instr);
	
	// register file logic
	regfile	rf(clk, RegWrite, Instr[19:15], Instr[24:20],
					Instr[11:7], Result, RD1, RD2);
	extend	ext(Instr[31:7], ImmSrc, ImmExt);
	
	//2 input register for A and WriteData
	flopr2 #(32) rdreg(clk, reset, 1'b1, RD1, RD2, A, WriteData);
	
	//ALU logic
	mux3 #(32) SAmux(PC, OldPC, A, ALUSrcA, SrcA);
	mux3 #(32) SBmux(WriteData, ImmExt, 32'd4, ALUSrcB, SrcB);
	alu	alu(SrcA, SrcB, ALUControl, ALUResult, Zero);
	
	//Result logic
	
	//resultmux 00
	flopr #(32) aluoutreg(clk, reset, 1'b1, ALUResult, ALUOut);
	//fed to resultmux 01
	flopr #(32) datareg(clk, reset, 1'b1, ReadData, Data);
	//result mux
	mux3 #(32) resmux(ALUOut, Data, ALUResult, ResultSrc, Result);
endmodule

module flopr #(parameter WIDTH = 8)
              (input  logic             clk, reset, enable,
               input  logic [WIDTH-1:0] d, 
               output logic [WIDTH-1:0] q);

  always_ff @(posedge clk, posedge reset)
    if (reset) 		q <= 0;
    else if (enable)	q <= d;
endmodule

module flopr2 #(parameter WIDTH = 8)
               (input  logic             clk, reset, enable,
                input  logic [WIDTH-1:0] d0, d1, 
                output logic [WIDTH-1:0] q0, q1);

  always_ff @(posedge clk, posedge reset)
    if (reset)
      begin
        q0 <= 0;
        q1 <= 0;
      end
    else if (enable)
      begin
        q0 <= d0;
        q1 <= d1;
      end

endmodule

//This parameter as well for the same reasons
module mux2 #(parameter WIDTH = 8)
             (input  logic [WIDTH-1:0] d0, d1, 
              input  logic             s, 
              output logic [WIDTH-1:0] y);

  assign y = s ? d1 : d0; 
endmodule

//And this one
module mux3 #(parameter WIDTH = 8)
             (input  logic [WIDTH-1:0] d0, d1, d2,
              input  logic [1:0]       s, 
              output logic [WIDTH-1:0] y);

  assign y = s[1] ? d2 : (s[0] ? d1 : d0); 
endmodule

module regfile(input  logic        clk, 
               input  logic        we3, 
               input  logic [ 4:0] a1, a2, a3, 
               input  logic [31:0] wd3, 
               output logic [31:0] rd1, rd2);

  logic [31:0] rf[31:0];

  // three ported register file
  // read two ports combinationally (A1/RD1, A2/RD2)
  // write third port on rising edge of clock (A3/WD3/WE3)
  // register 0 hardwired to 0

  always_ff @(posedge clk)
    if (we3) rf[a3] <= wd3;	

  assign rd1 = (a1 != 0) ? rf[a1] : 0;
  assign rd2 = (a2 != 0) ? rf[a2] : 0;
endmodule

module extend(input  logic [31:7] instr,
              input  logic [1:0]  immsrc,
              output logic [31:0] immext);
 
  always_comb
    case(immsrc) 
               // I-type 
      2'b00:   immext = {{20{instr[31]}}, instr[31:20]};  
               // S-type (stores)
      2'b01:   immext = {{20{instr[31]}}, instr[31:25], instr[11:7]};
               // B-type (branches)
      2'b10:   immext = {{19{instr[31]}}, instr[7], instr[30:25], instr[11:8], 1'b0};
               // J-type (jal)
      2'b11:   immext = {{12{instr[31]}}, instr[19:12], instr[20], instr[30:21], 1'b0};
      default: immext = 32'bx; // undefined
    endcase             
endmodule
					 

module id_mem(input logic			 clk, we,
				  input logic  [31:0] a, wd,
				  output logic	[31:0] rd);
  //Memory
  logic [31:0] RAM[63:0];
  
  initial
		$readmemh("riscvtest.txt", RAM);	//read test code from memory file
		
  assign rd = RAM[a[31:2]]; //word aligned
  
  always_ff @(posedge clk)
	 if (we) RAM[a[31:2]] <= wd;
endmodule

module controller(input logic clk,
						input logic reset,
						input logic [6:0] op,
						input logic [2:0] funct3,
						input logic funct7b5,
						input logic zero,
						output logic [1:0] immsrc,
						output logic [1:0] alusrca, alusrcb,
						output logic [1:0] resultsrc,
						output logic adrsrc,
						output logic [2:0] alucontrol,
						output logic irwrite, pcwrite,
						output logic regwrite, memwrite);
	
	logic [1:0] ALUOp;
	logic			Branch;
	logic 		PCUpdate;
	
	//Enumerate controller FSM states
	typedef enum logic [3:0] {Fetch, Decode, MemAdr, MemRead, MemWB, MemWrite, ExecuteR, ALUWB, ExecuteI, JAL, BEQ} statetype;
	statetype state, nextstate;
	
	//state register
	always_ff @(posedge clk, posedge reset)
		if(reset)	state <= Fetch; //Go back to the first state - Fetch
		else			state <= nextstate;
	
	//Next state logic
	always_comb begin
		case(state)
			Fetch:	if(reset)	nextstate = Fetch;
						else			nextstate = Decode;
			Decode:	case(op)
							7'b0000011, 7'b0100011:	nextstate = MemAdr; // {lw, sw} Both op codes map to the same nextstate
							7'b0110011:	nextstate = ExecuteR;	// R-type
							7'b0010011:	nextstate = ExecuteI;	// I-type ALU
							7'b1101111:	nextstate = JAL;			// jal
							7'b1100011:	nextstate = BEQ;			// beq
							default:	nextstate = Decode;	// remain in this state
						endcase
			MemAdr:	case(op)
							7'b0000011: nextstate = MemRead;
							7'b0100011:	nextstate = MemWrite;	
							default:	nextstate = MemAdr;
						endcase
			
			MemRead:	 nextstate = MemWB;
			ExecuteR, ExecuteI, JAL:		nextstate = ALUWB;
			MemWB, MemWrite, ALUWB, BEQ:	nextstate = Fetch;
			
			default:  nextstate = Fetch;	// default state
		endcase
	end
	
	/*
	Default output values:
							alusrca = 2'b00;
							alusrcb = 2'b00;
							resultsrc = 2'b00;
							adrsrc = 1'b0;
							ALUOp = 2'b00;
							irwrite = 1'b0;
							Branch = 1'b0;
							PCUpdate = 1'b0;
							regwrite = 1'b0;
							memwrite = 1'b0;
	*/
	
	//Output logic
	
	always_comb begin
        case(state)
            Fetch:	begin
							//setting output register values
							adrsrc = 1'b0;
							irwrite = 1'b1;
							alusrca = 2'b00;
							alusrcb = 2'b10;
							resultsrc = 2'b10;
							//sets alucontrol value
							ALUOp = 2'b00;
							//sets pcwrite value
							Branch = 1'b0;
							PCUpdate = 1'b1;
							
							//When outputs are don’t care, set them to 0 so they have a deterministic value to simplify testing
							regwrite = 1'b0;
							memwrite = 1'b0;
							end
				Decode:	begin
							//set
							alusrca = 2'b01;
							alusrcb = 2'b01;
							
							ALUOp = 2'b00;
							
							Branch = 1'b0;
							PCUpdate = 1'b0;
							
							//don't care
							resultsrc = 2'b00;
							adrsrc = 1'b0;
							irwrite = 1'b0;
							regwrite = 1'b0;
							memwrite = 1'b0;
							end
				MemAdr:	begin
							//set
							alusrca = 2'b10;
							alusrcb = 2'b01;
							
							ALUOp = 2'b00;
							
							Branch = 1'b0;
							PCUpdate = 1'b0;
							
							//don't care
							resultsrc = 2'b00;
							adrsrc = 1'b0;
							irwrite = 1'b0;
							regwrite = 1'b0;
							memwrite = 1'b0;
							end
				MemRead:	begin
							//set
							resultsrc = 2'b00;
							adrsrc = 1'b1;
							
							ALUOp = 2'b00;
							
							Branch = 1'b0;
							PCUpdate = 1'b0;
							
							//don't care
							alusrca = 2'b00;
							alusrcb = 2'b00;
							irwrite = 1'b0;
							regwrite = 1'b0;
							memwrite = 1'b0;
							end
				MemWB:	begin
							//set
							resultsrc = 2'b01;
							regwrite = 1'b1;
							
							ALUOp = 2'b00;
							
							Branch = 1'b0;
							PCUpdate = 1'b0;
							
							//don't care
							alusrca = 2'b00;
							alusrcb = 2'b00;
							adrsrc = 1'b0;
							irwrite = 1'b0;
							memwrite = 1'b0;
							end
				MemWrite:begin
							//set
							resultsrc = 2'b00;
							adrsrc = 1'b1;
							memwrite = 1'b1;
							
							ALUOp = 2'b00;
							
							Branch = 1'b0;
							PCUpdate = 1'b0;
							
							//don't care
							alusrca = 2'b00;
							alusrcb = 2'b00;
							irwrite = 1'b0;
							regwrite = 1'b0;
							end
				ExecuteR:begin
							//set
							alusrca = 2'b10;
							alusrcb = 2'b00;
							
							ALUOp = 2'b10;
							
							Branch = 1'b0;
							PCUpdate = 1'b0;
							
							//don't care
							resultsrc = 2'b00;
							adrsrc = 1'b0;
							irwrite = 1'b0;
							regwrite = 1'b0;
							memwrite = 1'b0;
							end
				ALUWB:	begin
							//set
							resultsrc = 2'b00;
							regwrite = 1'b1;
							
							ALUOp = 2'b00;
							
							Branch = 1'b0;
							PCUpdate = 1'b0;
							
							//don't care
							alusrca = 2'b00;
							alusrcb = 2'b00;
							adrsrc = 1'b0;
							irwrite = 1'b0;
							memwrite = 1'b0;
							end
				ExecuteI:begin
							//set
							alusrca = 2'b10;
							alusrcb = 2'b01;
							
							ALUOp = 2'b10;
							
							Branch = 1'b0;
							PCUpdate = 1'b0;
							
							//don't care
							resultsrc = 2'b00;
							adrsrc = 1'b0;
							irwrite = 1'b0;
							regwrite = 1'b0;
							memwrite = 1'b0;
							end
				JAL:		begin
							//set
							alusrca = 2'b01;
							alusrcb = 2'b10;
							resultsrc = 2'b00;
							
							ALUOp = 2'b00;
							
							Branch = 1'b0;
							PCUpdate = 1'b1;
							
							//don't care
							adrsrc = 1'b0;
							irwrite = 1'b0;
							regwrite = 1'b0;
							memwrite = 1'b0;
							end
				BEQ:		begin
							//set
							alusrca = 2'b10;
							alusrcb = 2'b00;
							resultsrc = 2'b00;
							
							ALUOp = 2'b01;
							
							Branch = 1'b1;
							PCUpdate = 1'b0;
							
							//don't care
							adrsrc = 1'b0;
							irwrite = 1'b0;
							regwrite = 1'b0;
							memwrite = 1'b0;
							end
            default: begin
							//matches values at Fetch state
							adrsrc = 1'b0;
							irwrite = 1'b1;
							alusrca = 2'b00;
							alusrcb = 2'b10;
							resultsrc = 2'b10;
							//sets alucontrol value
							ALUOp = 2'b00;
							//sets pcwrite value
							Branch = 1'b0;
							PCUpdate = 1'b1;
							
							//don't care
							regwrite = 1'b0;
							memwrite = 1'b0;
							end
        endcase
    end
	 
	//aludec module instance for alucontrol
	aludec ad(op[5], funct3, funct7b5, ALUOp, alucontrol);
	
	//instrdec module instance	for immsrc
	instrdec id(op, immsrc);
	
	assign pcwrite = Branch & zero | PCUpdate; // define pcwrite signal
	 
endmodule

module aludec(input logic opb5,
	 input logic [2:0] funct3,
	 input logic funct7b5,
	 input logic [1:0] ALUOp,
	 output logic [2:0] ALUControl);
	 logic RtypeSub;
	 assign RtypeSub = funct7b5 & opb5; // TRUE for R-type subtract instruction
	 always_comb
		case(ALUOp)
			2'b00: ALUControl = 3'b000; // addition
			2'b01: ALUControl = 3'b001; // subtraction
			default: case(funct3) // R-type or I-type ALU
							3'b000: if (RtypeSub)
											ALUControl = 3'b001; // sub
									  else
											ALUControl = 3'b000; // add, addi
							3'b010: ALUControl = 3'b101; // slt, slti
							3'b110: ALUControl = 3'b011; // or, ori
							3'b111: ALUControl = 3'b010; // and, andi
							default: ALUControl = 3'bxxx; // ???
						endcase
	 endcase
endmodule

module alu(input  logic [31:0] a, b,
           input  logic [2:0]  alucontrol,
           output logic [31:0] result,
           output logic        zero);

  logic [31:0] condinvb, sum;
  logic        v;              // overflow
  logic        isAddSub;       // true when is add or subtract operation

  assign condinvb = alucontrol[0] ? ~b : b;
  assign sum = a + condinvb + alucontrol[0];
  assign isAddSub = ~alucontrol[2] & ~alucontrol[1] |
                    ~alucontrol[1] & alucontrol[0];

  always_comb
    case (alucontrol)
      3'b000:  result = sum;                 // add
      3'b001:  result = sum;                 // subtract
      3'b010:  result = a & b;               // and
      3'b011:  result = a | b;       			// or
      3'b100:  result = a ^ b;      			// xor
      3'b101:  result = (a < b) ? 1 : 0;     // slt
      3'b110:  result = a << b;       			// sll
      3'b111:  result = a >> b;      			// srl
      default: result = 32'bx;
    endcase

  assign zero = (result == 32'b0);
  assign v = ~(alucontrol[0] ^ a[31] ^ b[31]) & (a[31] ^ sum[31]) & isAddSub;
  
endmodule

module instrdec (input logic [6:0] op,
					  output logic [1:0] ImmSrc);
	 always_comb
		case(op)
		 7'b0110011: ImmSrc = 2'b00; // R-type - should be XX but testbench expects 00 instead of don't cares
		 7'b0010011: ImmSrc = 2'b00; // I-type ALU
		 7'b0000011: ImmSrc = 2'b00; // lw
		 7'b0100011: ImmSrc = 2'b01; // sw
		 7'b1100011: ImmSrc = 2'b10; // beq
		 7'b1101111: ImmSrc = 2'b11; // jal
		 default: ImmSrc = 2'bxx; // ???
		endcase
endmodule