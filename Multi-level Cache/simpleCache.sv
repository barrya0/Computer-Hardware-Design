/*
-Direct-mapped cache
-write-back using write allocate
-block size: 4 words (16 bytes / 128 bits)
-Cache size:  8 KiB (512 blocks in total)
-32-bit address
-The cache includes a valid bit and dirty bit per block
-Decide address fields
-Byte offset: 2 bits
-Block offset: 2 bits
-Cache index: 8 bits
-Tag size: 20 bits = 32 - (8+2+2)
-non-blocking
*/
//creating cacheline Package to be used in simplecache module
package cacheLinePackage;
    //creating cacheline object
    typedef struct {
        logic valid;
        logic dirty;
        logic [19:0] tag; //20 bits bc tag = 28-index(8) = 20
        logic [127:0] block; //data block is 4 words each being 32 bits
    } cacheLine;
endpackage

import cacheLinePackage::*;

//Pretty Rudimentary testbench currently
module testbench();
	//initialize signals
	logic clk;
	logic reset;
	
	logic read, write, valid, ready, write_enable;
	logic [31:0] Address, word_to_cache, word_to_cpu;
	logic [127:0] block_to_mem;
	logic [127:0] memData;
	//instantiate main memory unit
	memory #(32, 128) mem(Address, block_to_mem, write_enable, memData);
	//create dut
	simpleCache dut(clk, reset, read, write, valid, write_enable, 
						Address, word_to_cache, word_to_cpu, 
						block_to_mem, memData, ready);

	//initialize test
	initial
		begin
			reset <= 1; # 22; reset <= 0;
		end
	//generate clock to sequence tests
	always
		begin
			clk <=1; #5; clk <= 0; #5;
		end
	initial begin
		logic [31:0] addresses[0:19];	//create an array of 32-bit addresses
		logic [127:0] data[0:19];		//array of 128-bit data corresponding to each address
		
		//Initialize signals
		read = 0;
		write = 0;
		valid = 0;
		write_enable = 0;
		Address = '0;
		word_to_cache = '0;
		memData = '0;
		
		//fill the arrays with random data
		for(int i = 0; i < 20; i++) begin
			addresses[i] = $urandom;
			data[i] = {$urandom(), $urandom()};
		end
		//write it to memory unit
		for(int i = 0; i < 20; i++) begin
			write_enable = 1;
			Address = addresses[i];
			block_to_mem = data[i];
			
			#5;
			
			$display("Write %0d: Address = %0h, Data = %0h", i+1, Address, block_to_mem);
		end
		
		//Test 1: read miss
		/*
		-Cache should see the read, miss in compareTag state
		-Enter Allocate state as the dirty bit is low
		-Bring memData at the address into the cacheline
		-Return to compareTag and get a hit
		-Word_to_cpu should be set based on the wordOff
		-Should go to Idle and ready signal set high
		*/
		read = 1;
		write = 0;
		valid = 1;
		Address = addresses[5];
		memData = data[5];
		
		#40; //wait for 40 time units or 4 clock cycles
		valid = 0;
		#5;
		//Test 2: write miss
		/*
		-Cache should see the write, miss in the compareTag state but set the dirty bit to high
		-Oldblock is clean here so next is
		-Allocate and read the block into memory
		-Back to compareTag, get a hit
		-random word_to_cache should be set based on wordOff
		-Should go to Idle and ready set high
		*/
		read = 0;
		write = 1;
		valid = 1;
		Address = addresses[2];
		memData = data[2];
		word_to_cache = $urandom;
		
		#40;
		valid = 0;
		#5;
		//Test 3: read hit
		/*
		-Cache sees the read, hits in compareTag
		-Sets word_to_cpu based on wordOff and goes back to Idle
		-Ready set high
		*/
		read = 1;
		write = 0;
		valid = 1;
		Address = addresses[5];
		#20;
		valid = 0;
		#5;
		//Test 4: Write-Back
		/*
		-Cache sees the read on dirty data
		-Go to writeBack state and write dirty data to memory
		-Allocate new block from memory
		-CompareTag state should set dirty bit back to 0 on read or remain 1 on write
		-CompareTag should set data back to valid
		-Go to Idle state, set ready high
		*/
		read = 1;
		write = 0;
		valid = 1;
		Address = addresses[2];
		memData = data[2];
		#50;
		valid = 0;
		#5;
	end
endmodule
module simpleCache(input logic clk, reset,
				 input logic read, write, valid,
				 output logic write_enable,
				 input logic [31:0] cpuAddr, word_to_cache/*word*/,
				 output logic [31:0] word_to_cpu,
				 output logic [127:0] block_to_mem,
				 input logic [127:0] memData,
				 output logic ready);
	 //Define the address tag, index, block and byte offset from 32 bit Addr
    logic [7:0] index;
    logic [1:0] wordOff;
	 logic [1:0] byteOff;
    logic [19:0] addrTag;
    assign {addrTag, index, wordOff, byteOff/*for byte addressing-ignore for now*/} = cpuAddr;
    
    //Number of rows = 2^k where k = cache index -> 2^8 = 256
    parameter int rows = 256;
    //create array of cacheline objects
    cacheLine cacheTable [0:rows-1];
	 //initialize the table with default 0
	 initial begin
		 for (int i = 0; i < rows; i++) begin
			cacheTable[i].valid = 1'b0;
			cacheTable[i].dirty = 1'b0;
			cacheTable[i].tag = 20'b0;
			cacheTable[i].block = 128'b0;
		 end
	 end
    cacheLine newCacheLine;
    
    cacheFSM controller(clk, reset, read, write, valid, wordOff, addrTag, 
							word_to_cache, cacheTable[index], memData, write_enable, 
							block_to_mem, word_to_cpu, newCacheLine, ready);
    always_ff @(posedge clk) begin
        cacheTable[index] = newCacheLine; //update cacheline on clock edge
    end
endmodule

module cacheFSM(input logic clk, reset,
					 input logic read, write, valid,
					 input logic [1:0] wordOff,
					 input logic [19:0] addrTag,
					 input logic [31:0] word_to_cache,
					 input cacheLine oldCL /*using cacheline struct in fsm*/,
					 input logic [127:0] memData,
					 output logic w_e,
					 output logic [127:0] block_to_mem,
					 output logic [31:0] word_to_cpu,
					 output cacheLine newCL,
					 output logic ready);
 
	//Enumerate Cache Controller States
	typedef enum {idle, compareTag, allocate, writeBack} fsm_states;

	fsm_states state, nextstate;

	//state register
	always_ff @(posedge clk) begin
	  if (reset)    state <= idle;
	  else          state <= nextstate;
	end

	//transition and output logic logic
	always_comb begin
		//default values to avoid inferring latches
		ready <= 1'b0;
		block_to_mem <= '0;
		newCL <= oldCL;
		word_to_cpu <= '0;
		w_e <= 1'b0;
	  case(state)
			idle: begin
						if(valid)	nextstate = compareTag;
						else begin
							nextstate = idle;
							ready <= 1'b1;
						end
					end
			compareTag:	begin
							  if(write) begin
									newCL.dirty <= 1'b1; //on first write to the cacheline, set dirty bit to 0
									newCL.valid <= 1'b0;	//data invalidated, should be written to memory
							  end
							  if(oldCL.valid && (oldCL.tag == addrTag)) begin //check if tag from cacheline is equal to cpu address tag
									//cache hit
									nextstate = idle;
									if(read) begin
										//read the word from the datablock in the cache using the offset
										case(wordOff)
											2'b00:	word_to_cpu <= {oldCL.block[127:96]};
											2'b01:	word_to_cpu <= {oldCL.block[95:64]};
											2'b10:	word_to_cpu <= {oldCL.block[63:32]};
											2'b11:	word_to_cpu <= {oldCL.block[31:0]};
										endcase
									end	
									else if(write) begin
										//write word from cpu to cache using offset
										case(wordOff)
											2'b00:	newCL.block[127:96] <= word_to_cache;
											2'b01:	newCL.block[95:64] <= word_to_cache;
											2'b10:	newCL.block[63:32] <= word_to_cache;
											2'b11:	newCL.block[31:0] <= word_to_cache;
										endcase
									end
							  end else begin //miss
									nextstate = oldCL.dirty ? writeBack : allocate; /*cache miss and old block is dirty : cache miss and old block is clean*/
									//set valid
									newCL.valid <= 1'b1;
									//set tag
									newCL.tag <= addrTag;
							  end
						  end
			writeBack:	begin
							  //write old block to memory datain
							  //write_enable
							  w_e <= 1'b1;
							  block_to_mem <= oldCL.block;
							  nextstate = allocate;
							end
			allocate:	begin
							  //read new block from memory
							  newCL.valid <= 1'b1; //Validate the block when a new block is allocated to it
							  newCL.dirty <= 1'b0; //set dirty back to low, cacheline is clean
							  newCL.block <= memData;
							  nextstate = compareTag;
							end
			default:    begin
								 nextstate = idle;
							end
	  endcase
	end
endmodule

module memory #(parameter ADDR_WIDTH = 32, DATA_WIDTH = 128)(
	input logic [ADDR_WIDTH-1:0] address,
	input logic [DATA_WIDTH-1:0] write_data,
	input logic write_enable,
	output logic [DATA_WIDTH-1:0] read_data
);
	//memory array
	logic [DATA_WIDTH-1:0] mem[2**ADDR_WIDTH-1:0];
	
	//write operation
	always_ff@(posedge write_enable) begin
		if(address < 2**ADDR_WIDTH) begin
			mem[address] <= write_data;
		end
	end
	
	//read operation
	assign read_data = (address < 2**ADDR_WIDTH) ? mem[address] : 1'b0;
endmodule