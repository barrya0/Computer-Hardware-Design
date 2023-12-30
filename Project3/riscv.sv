module testbench();

  logic        clk;
  logic        reset;

  logic [31:0] WriteData, DataAdr;
  logic        MemWrite;

  // instantiate device to be tested
  top dut(clk, reset, WriteData, DataAdr, MemWrite);
  
  // initialize test
  initial
    begin
      reset <= 1; # 22; reset <= 0;
    end

  // generate clock to sequence tests
  always
    begin
      clk <= 1; # 5; clk <= 0; # 5;
    end

  // check results
  always @(negedge clk)
    begin
      if(MemWrite) begin
        if(DataAdr === 100 & WriteData === 25) begin
          $display("Simulation succeeded");
          $stop;
        end else if (DataAdr !== 96) begin
          $display("Simulation failed");
          $stop;
        end
      end
    end
endmodule
///////////////////////////////////////////////////////////
///// End Testbench                                   /////
///////////////////////////////////////////////////////////

module top(input logic clk, reset,
 output logic [31:0] WriteDataM, DataAdrM,
 output logic MemWriteM);
 logic [31:0] PCF, InstrF, ReadDataM;

 // instantiate processor and memories
 riscv riscv(clk, reset, PCF, InstrF, MemWriteM, DataAdrM,
 WriteDataM, ReadDataM);
 imem imem(PCF, InstrF);
 dmem dmem(clk, MemWriteM, DataAdrM, WriteDataM, ReadDataM);
endmodule

module riscv(input logic clk, reset,
				 output logic [31:0] PCF,
				 input logic  [31:0] InstrF,
				 output logic MemWriteM,
				 output logic [31:0] ALUResultM, WriteDataM,
				 input logic [31:0] ReadDataM);
	//Defining the signals that the controller, datapath, and hazard units need
	logic ALUSrcE, RegWriteM, RegWriteW, PCSrcE, ZeroE, luiE, luidec; //added lui signal
	logic StallF, StallD, FlushD, FlushE, ResultSrcE0;
	logic [2:0] ALUControlE;
	logic [1:0] ImmSrcD, ResultSrcW, ForwardAE, ForwardBE;
	logic [31:0] InstrD;
	logic [4:0] Rs1D, Rs2D, Rs1E, Rs2E, RdE, RdM, RdW;
	
	
	controller	c(clk, reset, InstrD[6:0], InstrD[14:12], InstrD[30], ZeroE, FlushE, ResultSrcE0, ResultSrcW, MemWriteM, PCSrcE, ALUSrcE, RegWriteM, RegWriteW, ImmSrcD, ALUControlE, /*output*/luiE, /*output*/ luidec);
	
	hazardunit	h(Rs1D, Rs2D, Rs1E, Rs2E, RdE, RdM, RdW, RegWriteM, RegWriteW, ResultSrcE0, PCSrcE, ForwardAE, ForwardBE, StallD, StallF, FlushD, FlushE);
	
	datapath		dp(clk, reset, ResultSrcW, PCSrcE, ALUSrcE, RegWriteW, ImmSrcD, ALUControlE, ZeroE, PCF, InstrF, InstrD, ALUResultM, WriteDataM, ReadDataM, ForwardAE, ForwardBE, Rs1D, Rs2D, Rs1E, Rs2E, RdE, RdM, RdW, StallD, StallF, FlushD, FlushE, /*input*/luiE, /*input*/luidec);
	
endmodule
				 
module controller(input logic clk, reset,
						input logic [6:0] op,
						input logic [2:0] funct3,
						input logic funct7b5,
						input logic ZeroE,
						input logic FlushE,
						output logic ResultSrcE0,
						output logic [1:0] ResultSrcW,
						output logic MemWriteM,
						output logic PCSrcE, ALUSrcE,
						output logic RegWriteM, RegWriteW,
						output logic [1:0] ImmSrcD,
						output logic [2:0] ALUControlE,
						output logic luiE,
						output logic luidec);
	logic [1:0] ALUOpD;
	logic [1:0] ResultSrcD, ResultSrcE, ResultSrcM;
	logic [2:0] ALUControlD;
	logic luiD;
	logic BranchD, BranchE, JumpD, JumpE, MemWriteD, MemWriteE, RegWriteD, RegWriteE, ALUSrcD;
	
	
	//instantiate main decoder
	maindec md(op, ResultSrcD, MemWriteD, BranchD, ALUSrcD, RegWriteD, JumpD, ImmSrcD, ALUOpD, luiD, luidec);
	
	//alu decoder
	aludec ad(op[5], funct3, funct7b5, ALUOpD, ALUControlD);
	
	//Controller pipelined registers
	Con_pipereg0 c_pipe0(clk, reset, FlushE, RegWriteD, MemWriteD, JumpD, BranchD, ALUSrcD, ALUControlD, ResultSrcD, ResultSrcE, RegWriteE, MemWriteE, JumpE, BranchE, ALUSrcE, ALUControlE, luiD, luiE);
	
	
	Con_pipereg1 c_pipe1(clk, reset, RegWriteE, MemWriteE, ResultSrcE, RegWriteM, MemWriteM, ResultSrcM);
	
	Con_pipereg2 c_pipe2(clk, reset, RegWriteM, ResultSrcM, RegWriteW, ResultSrcW);
	
	//more output logic
	assign ResultSrcE0 = ResultSrcE[0];
	always_comb begin
		PCSrcE = JumpE | (BranchE & ZeroE);
	end
	
endmodule

module Con_pipereg0(input logic clk, reset, clear,
        input logic RegWriteD, MemWriteD, JumpD, BranchD, ALUSrcD,
		  input logic [2:0] ALUControlD,
        input logic [1:0] ResultSrcD,
		  output logic [1:0] ResultSrcE,	  
        output logic RegWriteE, MemWriteE, JumpE, BranchE, ALUSrcE,
        output logic [2:0] ALUControlE,
		  input logic luiD, //for lui
		  output logic luiE);

	always_ff @( posedge clk, posedge reset ) begin

			if (reset) begin
				RegWriteE <= 0;
				MemWriteE <= 0;
				JumpE <= 0;
				BranchE <= 0; 
				ALUSrcE <= 0;
				ResultSrcE <= 0;
				ALUControlE <= 0;
				luiE <= 0;
			end

			else if (clear) begin
				RegWriteE <= 0;
				MemWriteE <= 0;
				JumpE <= 0;
				BranchE <= 0; 
				ALUSrcE <= 0;
				ResultSrcE <= 0;
				ALUControlE <= 0;
				luiE <= 0;
			end
			
			else begin
				RegWriteE <= RegWriteD;
				MemWriteE <= MemWriteD;
				JumpE <= JumpD;
				BranchE <= BranchD; 
				ALUSrcE <= ALUSrcD;
				ResultSrcE <= ResultSrcD;
				ALUControlE <= ALUControlD;
				luiE <= luiD;
			end
			 
		 end
  
endmodule

module Con_pipereg1(input logic clk, reset,
                input logic RegWriteE, MemWriteE,
                input logic [1:0] ResultSrcE,  
                output logic RegWriteM, MemWriteM,
                output logic [1:0] ResultSrcM);

    always_ff @( posedge clk, posedge reset ) begin
        if (reset) begin
            RegWriteM <= 0;
            MemWriteM <= 0;
            ResultSrcM <= 0;
        end
        else begin
            RegWriteM <= RegWriteE;
            MemWriteM <= MemWriteE;
            ResultSrcM <= ResultSrcE; 
        end
        
    end

endmodule

module Con_pipereg2(input logic clk, reset, 
                input logic RegWriteM, 
                input logic [1:0] ResultSrcM, 
                output logic RegWriteW, 
                output logic [1:0] ResultSrcW);

    always_ff @( posedge clk, posedge reset ) begin
        if (reset) begin
            RegWriteW <= 0;
            ResultSrcW <= 0;           
        end

        else begin
            RegWriteW <= RegWriteM;
            ResultSrcW <= ResultSrcM;
        end
    end

endmodule

module maindec(input  logic [6:0] op,
               output logic [1:0] ResultSrc,
               output logic       MemWrite,
               output logic       Branch, ALUSrc,
               output logic       RegWrite, Jump,
               output logic [1:0] ImmSrc,
               output logic [1:0] ALUOp,
					output logic luiD,
					output logic luidec);

  logic [11:0] controls;

  assign {RegWrite, ImmSrc, ALUSrc, MemWrite,
          ResultSrc, Branch, ALUOp, Jump, luiD} = controls;

  always_comb
    case(op)
    // RegWrite_ImmSrc_ALUSrc_MemWrite_ResultSrc_Branch_ALUOp_Jump
      7'b0000011: controls = 12'b1_00_1_0_01_0_00_0_0; // lw
      /////////////////////////////////////////////////
      // Write more operators here                   //
      //                                             // sw
		7'b0100011: controls = 12'b0_01_1_1_00_0_00_0_0;
      //                                             // R-type
		7'b0110011: controls = 12'b1_00_0_0_00_0_10_0_0;
      //                                             // beq
		7'b1100011: controls = 12'b0_10_0_0_00_1_01_0_0;
      //                                             // I-type ALU
		7'b0010011: controls = 12'b1_00_1_0_00_0_10_0_0;
      //                                             // jal
		7'b1101111: controls = 12'b1_11_0_0_10_0_00_1_0;
      /////////////////////////////////////////////////
		7'b0110111: controls = 12'b1_00_1_0_00_0_00_0_1; //lui instr -make alusrc 1 to choose the immextE in the datapath, make the aluop 00 so it adds
      default:    controls = 12'b0_00_0_0_00_0_00_0_0; // non-implemented instruction
    endcase
	assign luidec = luiD;
endmodule

module aludec(input  logic       opb5,
              input  logic [2:0] funct3,
              input  logic       funct7b5, 
              input  logic [1:0] ALUOp,
              output logic [2:0] ALUControl);

  logic  RtypeSub;
  assign RtypeSub = funct7b5 & opb5;  // TRUE for R-type subtract instruction

  always_comb
    case(ALUOp)
      2'b00:                ALUControl = 3'b000; // addition
      2'b01:                ALUControl = 3'b001; // subtraction
      default: case(funct3) // R-type or I-type ALU
                 3'b000:  if (RtypeSub) 
                            ALUControl = 3'b001; // sub
                          else          
                            ALUControl = 3'b000; // add, addi
					  3'b001:	 ALUControl = 3'b110; // sll
                 3'b010:    ALUControl = 3'b101; // slt, slti
                 3'b110:    ALUControl = 3'b011; // or, ori
                 3'b111:    ALUControl = 3'b010; // and, andi
                 default:   ALUControl = 3'b000; // ???
               endcase
    endcase
endmodule

module hazardunit(input logic [4:0] Rs1D, Rs2D, Rs1E, Rs2E,
                input logic [4:0] RdE, RdM, RdW,
                input logic RegWriteM, RegWriteW,
				    input logic ResultSrcE0, PCSrcE,
                output logic [1:0] ForwardAE, ForwardBE,
                output logic StallD, StallF, FlushD, FlushE);
					 

	logic lwStall;
	always_comb begin
		  if ((Rs1E == RdM) & (RegWriteM) & (Rs1E != 0))
				ForwardAE = 2'b10; // forwarding ALU Result
		  else if ((Rs1E == RdW) & (RegWriteW) & (Rs1E != 0))
				ForwardAE = 2'b01; // forwarding WriteBack
		  else ForwardAE = 2'b00;
				

		  if ((Rs2E == RdM) & (RegWriteM) & (Rs2E != 0))
				ForwardBE = 2'b10; // forwarding ALU Result

		  else if ((Rs2E == RdW) & (RegWriteW) & (Rs2E != 0))
				ForwardBE = 2'b01; // forwarding WriteBack
		  else ForwardBE = 2'b00;
	  
	  end
	  
	// load word stall logic
   assign lwStall = ResultSrcE0 == 1'b1 & ((Rs1D == RdE) | (Rs2D == RdE));
	assign StallF = lwStall;
	assign StallD = lwStall;
	
	// control hazard
	assign FlushE = lwStall | PCSrcE;
	assign FlushD = PCSrcE;

endmodule

module datapath(input logic clk, reset,
		input logic [1:0] ResultSrcW,
		input logic PCSrcE, ALUSrcE,
		input logic RegWriteW,
		input logic [1:0] ImmSrcD,
		input logic [2:0] ALUControlE,
		output logic ZeroE,
		output logic [31:0] PCF,
		input logic [31:0] InstrF,
		output logic [31:0] InstrD,
		output logic [31:0] ALUResultM, WriteDataM,
		input logic [31:0] ReadDataM,
		input logic [1:0] ForwardAE, ForwardBE,
		output logic [4:0] Rs1D, Rs2D, Rs1E, Rs2E,
      output logic [4:0] RdE, RdM, RdW,
		input logic StallD, StallF, FlushD, FlushE,
		input logic luiE,
		input logic luidec);


	logic [31:0] PCD, PCE;
	logic [31:0] ALUResultE, ALUResultW, ReadDataW;
	logic [31:0] PCNextF, PCPlus4F, PCPlus4D, PCPlus4E, PCPlus4M, PCPlus4W, PCTargetE;
	logic [31:0] WriteDataE;
	logic [31:0] ResultW;
	logic [31:0] SrcAE, SrcBE, RD1D, RD2D, RD1E, RD2E, fSrcAE;
	logic [4:0] RdD; //address for dest. register
	logic [31:0] ImmExtD, ImmExtE;
	
	// Fetch
	mux2 #(32) pcnext(PCPlus4F, PCTargetE, PCSrcE, PCNextF);
	floppc #(32) pcfreg(clk, reset, ~StallF, PCNextF, PCF);
	adder pcadd4(PCF, 32'h4, PCPlus4F);
	
	// instruction fetch to instruction decode	
	
	if_to_id dpipe0 (clk, reset, FlushD, ~StallD, InstrF, PCF, PCPlus4F, InstrD, PCD, PCPlus4D);
	
	assign Rs1D = InstrD[19:15];
	assign Rs2D = InstrD[24:20];	
	assign RdD = InstrD[11:7];
	
	regfile rf (clk, RegWriteW, Rs1D, Rs2D, RdW, ResultW, RD1D, RD2D);	

	extend ext(InstrD[31:7], luidec, ImmSrcD, ImmExtD);
	
	//decode to execute
	
	id_to_iex dpipe1 (clk, reset, FlushE, RD1D, RD2D, PCD, Rs1D, Rs2D, RdD, ImmExtD, PCPlus4D, RD1E, RD2E, PCE, Rs1E, Rs2E, RdE, ImmExtE, PCPlus4E);
	
	mux3 #(32) srcamux(RD1E, ResultW, ALUResultM, ForwardAE, fSrcAE);
	
	//mux for lui
	mux2 #(32) fsrcamux(fSrcAE, 32'b0, luiE, SrcAE);
	
	mux3 #(32) fmuxB(RD2E, ResultW, ALUResultM, ForwardBE, WriteDataE);
	mux2 #(32) srcbmux(WriteDataE, ImmExtE, ALUSrcE, SrcBE);
	
	
	adder pcaddbranch(PCE, ImmExtE, PCTargetE);
	alu alu(SrcAE, SrcBE, ALUControlE, ALUResultE, ZeroE);
		
	//execute to memory
	
	iex_to_imem dpipe2 (clk, reset, ALUResultE, WriteDataE, RdE, PCPlus4E, ALUResultM, WriteDataM, RdM, PCPlus4M);
	
	//memory to register writeback
	imem_to_wb dpipe3(clk, reset, ALUResultM, ReadDataM, RdM, PCPlus4M, ALUResultW, ReadDataW, RdW, PCPlus4W);
	mux3 #(32) resultmux(ALUResultW, ReadDataW, PCPlus4W, ResultSrcW, ResultW);

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

  always_ff @(negedge clk)
    if (we3) rf[a3] <= wd3;	

  assign rd1 = (a1 != 0) ? rf[a1] : 0;
  assign rd2 = (a2 != 0) ? rf[a2] : 0;
endmodule

module adder(input  [31:0] a, b,
             output [31:0] y);

  assign y = a + b;
endmodule

module extend(input  logic [31:7] instr,
				  input logic lui, //add lui instruction
              input  logic [1:0]  immsrc,
              output logic [31:0] immext);
 
  always_comb
	 if(lui) begin
		immext = {instr[31:12], 12'b0};
	 end
    else begin
		 case(immsrc)
						// I-type 
			2'b00:   immext = {{20{instr[31]}}, instr[31:20]};  
						// S-type (stores)
			2'b01:   immext = {{20{instr[31]}}, instr[31:25], instr[11:7]};
						// B-type (branches)
			2'b10:   immext = {{19{instr[31]}}, instr[7], instr[30:25], instr[11:8], 1'b0};
						// J-type (jal)
			2'b11:   immext = {{12{instr[31]}}, instr[19:12], instr[20], instr[30:21], 1'b0};
			default: immext = 32'b0; // undefined
		 endcase
	 end
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
      default: result = 32'b0;
    endcase

  assign zero = (result == 32'b0);
  assign v = ~(alucontrol[0] ^ a[31] ^ b[31]) & (a[31] ^ sum[31]) & isAddSub;
  
endmodule

module floppc #(parameter WIDTH = 8)
 (input logic clk, reset, en,
 input logic [WIDTH-1:0] d,
output logic [WIDTH-1:0] q);
 always_ff @(posedge clk, posedge reset)
 if (reset) q <= 0;
 else if (en) q <= d;
endmodule

module mux3 #(parameter WIDTH = 8)
             (input  logic [WIDTH-1:0] d0, d1, d2,
              input  logic [1:0]       s, 
              output logic [WIDTH-1:0] y);

  assign y = s[1] ? d2 : (s[0] ? d1 : d0); 
endmodule

module if_to_id (input logic clk, reset, clear, enable,
            input logic [31:0] InstrF, PCF, PCPlus4F,
            output logic [31:0] InstrD, PCD, PCPlus4D);


	always_ff @( posedge clk, posedge reset ) begin
		 if (reset) begin // Asynchronous Clear
			  InstrD <= 0;
			  PCD <= 0;
			  PCPlus4D <= 0;
		 end

		 else if (enable) begin 
			 if (clear) begin // Synchrnous Clear
				  InstrD <= 0;
				  PCD <= 0;
				  PCPlus4D <= 0;	 
			 end
			 
			 else begin	 
				  InstrD <= InstrF;
				  PCD <= PCF;
				  PCPlus4D <= PCPlus4F;
			 end
		 end
	end

endmodule

module id_to_iex(input logic clk, reset, clear,
                 input logic [31:0] RD1D, RD2D, PCD, 
                 input logic [4:0] Rs1D, Rs2D, RdD, 
                 input logic [31:0] ImmExtD, PCPlus4D,
                 output logic [31:0] RD1E, RD2E, PCE, 
                 output logic [4:0] Rs1E, Rs2E, RdE, 
                 output logic [31:0] ImmExtE, PCPlus4E);

    always_ff @( posedge clk, posedge reset ) begin
        if (reset) begin
            RD1E <= 0;
            RD2E <= 0;
            PCE <= 0;
            Rs1E <= 0;
            Rs2E <= 0;
            RdE <= 0;
            ImmExtE <= 0;
            PCPlus4E <= 0;
        end

        else if (clear) begin
            RD1E <= 0;
            RD2E <= 0;
            PCE <= 0;
            Rs1E <= 0;
            Rs2E <= 0;
            RdE <= 0;
            ImmExtE <= 0;
            PCPlus4E <= 0;
        end
        else begin
            RD1E <= RD1D;
            RD2E <= RD2D;
            PCE <= PCD;
            Rs1E <= Rs1D;
            Rs2E <= Rs2D;
            RdE <= RdD;
            ImmExtE <= ImmExtD;
            PCPlus4E <= PCPlus4D;
        end
    end

endmodule

module iex_to_imem(input logic clk, reset,
                input logic [31:0] ALUResultE, WriteDataE, 
                input logic [4:0] RdE, 
                input logic [31:0] PCPlus4E,
                output logic [31:0] ALUResultM, WriteDataM,
                output logic [4:0] RdM, 
                output logic [31:0] PCPlus4M);

	always_ff @( posedge clk, posedge reset ) begin 
		 if (reset) begin
			  ALUResultM <= 0;
			  WriteDataM <= 0;
			  RdM <= 0; 
			  PCPlus4M <= 0;
		 end

		 else begin
			  ALUResultM <= ALUResultE;
			  WriteDataM <= WriteDataE;
			  RdM <= RdE; 
			  PCPlus4M <= PCPlus4E;        
		 end
		 
	end

endmodule

module imem_to_wb(input logic clk, reset,
                input logic [31:0] ALUResultM, ReadDataM,  
                input logic [4:0] RdM, 
                input logic [31:0] PCPlus4M,
                output logic [31:0] ALUResultW, ReadDataW,
                output logic [4:0] RdW, 
                output logic [31:0] PCPlus4W);

	always_ff @( posedge clk, posedge reset ) begin 
		 if (reset) begin
			  ALUResultW <= 0;
			  ReadDataW <= 0;
			  RdW <= 0; 
			  PCPlus4W <= 0;
		 end

		 else begin
			  ALUResultW <= ALUResultM;
			  ReadDataW <= ReadDataM;
			  RdW <= RdM; 
			  PCPlus4W <= PCPlus4M;        
		 end
		 
	end

endmodule

module mux2 #(parameter WIDTH = 8)
             (input  logic [WIDTH-1:0] d0, d1, 
              input  logic             s, 
              output logic [WIDTH-1:0] y);

  assign y = s ? d1 : d0; 
endmodule

module imem(input  logic [31:0] a,
            output logic [31:0] rd);

  logic [31:0] RAM[63:0];

  initial
      $readmemh("riscvtest.txt",RAM);

  assign rd = RAM[a[31:2]]; // word aligned
endmodule

module dmem(input  logic        clk, we,
            input  logic [31:0] a, wd,
            output logic [31:0] rd);

  logic [31:0] RAM[63:0];

  assign rd = RAM[a[31:2]]; // word aligned

  always_ff @(posedge clk)
    if (we) RAM[a[31:2]] <= wd;
endmodule