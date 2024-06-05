
`timescale 1ns/100ps

// ALU operations
   `define ADD  3'b000
   `define SUB  3'b001
   `define SLT  3'b010
   `define SLTU 3'b011
   `define AND  3'b100
   `define XOR  3'b101
   `define OR   3'b110
   `define NOR  3'b111

module multi_cycle_mips(

   input clk,
   input reset,

   // Memory Ports
   output  [31:0] mem_addr,
   input   [31:0] mem_read_data,
   output  [31:0] mem_write_data,
   output         mem_read,
   output         mem_write
);

   // Data Path Registers
   reg MemoryReadEnable, MemoryWriteEnable;
   reg [31:0] A, B, PC, IR, Data, MAR,JumpAddress, HiReg , LoReg;

   // Data Path Control Lines, don't forget, regs are not always register !!
   reg setMemoryReadEnable, clrMemoryReadEnable, setMemoryWriteEnable, clrMemoryWriteEnable;
   reg Awrt, Bwrt, RegWrite, PCwrt, IRwrt, Datawrt, MARwrt, jump,  HIwrt, LOwrt;

   // Memory Ports Bindings
   assign mem_addr = MAR;
   assign mem_read = MemoryReadEnable;
   assign mem_write = MemoryWriteEnable;
   assign mem_write_data = B;

   // Mux & ALU Control Line
   reg [2:0] aluOp;
   reg [1:0] ALUSrcB,RegDst;
   reg SgnExt, ALUSrcA, MemtoReg, IorD ,JumpControl,MultControl;

   reg[2:0] InputDataControl;

   // Wiring
   wire aluZero;
   wire [31:0] aluResult, rfRD1, rfRD2;
   wire [63:0] MultOutput;

   wire[31:0] PCJump = JumpControl ? {PC[31:28], IR[25:0] << 2} : A;

wire [31:0] temp2 = {16'b0,IR[15:0]};
   wire [31:0] temp = {temp2 << 16};
   
   // InputData Mux
   reg [31:0] InputData ;    
   always @(*)
   case (InputDataControl)
      3'b000: InputData = Data;
      3'b001: InputData = temp;
      3'b010: InputData = HiReg;
      3'b011: InputData = LoReg;
      3'b100: InputData = PC;
   endcase


   // Clocked Registers
   always @( posedge clk ) begin
      if( reset )
         PC <= #0.1 32'h00000000;
      else if( PCwrt ) begin
         if (jump)
            PC <= #0.1 PCJump;
         else
            PC <= #0.1 aluResult;
      end

      if( Awrt ) A <= #0.1 rfRD1;
      if( Bwrt ) B <= #0.1 rfRD2;

      if( MARwrt ) MAR <= #0.1 IorD ? aluResult : PC;

      if( IRwrt ) IR <= #0.1 mem_read_data;
      if( Datawrt ) Data <= #0.1 mem_read_data;

      if(HIwrt) HiReg <= #0.1 MultOutput[63:32];
      if(LOwrt) LoReg <= #0.1 MultOutput[31:0];

      if( reset | clrMemoryReadEnable ) MemoryReadEnable <= #0.1 1'b0;
          else if( setMemoryReadEnable) MemoryReadEnable <= #0.1 1'b1;

      if( reset | clrMemoryWriteEnable ) MemoryWriteEnable <= #0.1 1'b0;
          else if( setMemoryWriteEnable) MemoryWriteEnable <= #0.1 1'b1;
   end

   wire MultReady;

   // Register File
   reg_file rf(
      .clk( clk ),
      .write( RegWrite ),

      .RR1( IR[25:21] ),
      .RR2( IR[20:16] ),
      .RD1( rfRD1 ),
      .RD2( rfRD2 ),

      .WR( (RegDst==2'b10) ? 5'd31 :
           (RegDst==2'b01) ? IR[15:11] :
           IR[20:16] ),
      .WD( MemtoReg ? InputData : aluResult )
   );

   multiplier mult(
   .clk(clk),
   .start(MultControl),
   .A(A),
   .B(B),
   .hi(MultOutput[63:32]),
   .lo(MultOutput[31:0]),
   .ready(MultReady)
   );

   // Sign/Zero Extension
   wire [31:0] SZout = SgnExt ? {{16{IR[15]}}, IR[15:0]} : {16'h0000, IR[15:0]};

   // ALU-A Mux
   wire [31:0] aluA = ALUSrcA ? A : PC;

   // ALU-B Mux
   reg [31:0] aluB;
   always @(*)
   case (ALUSrcB)
      2'b00: aluB = B;
      2'b01: aluB = 32'h4;
      2'b10: aluB = SZout;
      2'b11: aluB = SZout << 2;
   endcase

   my_alu alu(
      .A( aluA ),
      .B( aluB ),
      .Op( aluOp ),

      .X( aluResult ),
      .Z( aluZero )
   );


   // Controller Starts Here

   // Controller State Registers
   reg [5:0] state, nxt_state;

   // State Names & Numbers
   localparam
      RESET = 0, FETCH1 = 1, FETCH2 = 2, FETCH3 = 3, DECODE = 4, EX_MULT_R1 = 5, EX_MULT_R2 = 6,
      EX_ALU_R = 7, EX_ALU_I = 8, EX_LUI = 9, 
      EX_LW_1 = 11, EX_LW_2 = 12, EX_LW_3 = 13, EX_LW_4 = 14, EX_LW_5 = 15, 
      EX_SW_1 = 21, EX_SW_2 = 22, EX_SW_3 = 23,
      EX_BNE_1 = 24,EX_BEQ_1 = 25, EX_BRA_2 = 26,
      EX_JUMP = 27, EX_JLINK = 28, EX_JUMP_R = 29,EX_JUMP_2 = 30,EX_JUMP_R2 = 31,
      EX_MOVE = 35 ;

   // State Clocked Register 
   always @(posedge clk)
      if(reset)
         state <= #0.1 RESET;
      else
         state <= #0.1 nxt_state;

   task PrepareFetch;
      begin
         IorD = 1'b0;
         setMemoryReadEnable = 1'b1;
         MARwrt = 1'b1;
         nxt_state = FETCH1;
      end
   endtask

   // State Machine Body Starts Here
   always @( * ) begin

      nxt_state = 1'bx;

      SgnExt = 1'bx; IorD = 1'bx;
      MemtoReg = 1'bx; RegDst = 2'bxx;
      ALUSrcA = 1'bx; ALUSrcB = 1'bx; aluOp = 1'bx;
      InputDataControl = 3'b000;
      JumpControl = 1'bx; MultControl = 1'b0;
      PCwrt = 1'b0;
      jump = 1'b0;
      Awrt = 1'b0; Bwrt = 1'b0;
      RegWrite = 1'b0; IRwrt = 1'b0;
      Datawrt = 1'b0; MARwrt = 1'b0;
      setMemoryReadEnable = 1'b0; clrMemoryReadEnable = 1'b0;
      setMemoryWriteEnable = 1'b0; clrMemoryWriteEnable = 1'b0;

      case(state)

         RESET:
            PrepareFetch;

         FETCH1:
            nxt_state = FETCH2;

         FETCH2:
            nxt_state = FETCH3;

         FETCH3: begin
            IRwrt = 1'b1; // IR <- Mem. Read Data
            PCwrt = 1'b1; // PC = PC + 4 write enable
            clrMemoryReadEnable = 1'b1; // Memory Read Enable = 0
            ALUSrcA = 1'b0; // PC
            ALUSrcB = 2'b01; // 4
            aluOp = `ADD;
            nxt_state = DECODE;
         end

         DECODE: begin
            Awrt = 1'b1;
            Bwrt = 1'b1;
            case( IR[31:26] ) // opcode
               6'b000_000:             // R-format
                  case( IR[5:3] )
                     3'b000: ;
                     3'b001: nxt_state = EX_JUMP_R; // jr , jalr
                     3'b010: nxt_state = EX_MOVE; // mfhi , mflo
                     3'b011: nxt_state = EX_MULT_R1; // mult , multu
                     3'b100: nxt_state = EX_ALU_R;
                     3'b101: nxt_state = EX_ALU_R;
                     3'b110: ;
                     3'b111: ;
                  endcase

               6'b001_000,             // addi
               6'b001_001,             // addiu
               6'b001_010,             // slti
               6'b001_011,             // sltiu
               6'b001_100,             // andi
               6'b001_101,             // ori
               6'b001_110:             // xori
                  nxt_state = EX_ALU_I;
         
               6'b100_011:
                  nxt_state = EX_LW_1;

               6'b101_011:
                  nxt_state = EX_SW_1;

               6'b000_100:
                  nxt_state = EX_BEQ_1;
               6'b000_101:
                  nxt_state = EX_BNE_1;
               6'b000010: nxt_state = EX_JUMP ;// j
               6'b000011: nxt_state = EX_JLINK ; // jal

               6'b001_111: nxt_state = EX_LUI ;   // lui

            endcase
         end

         EX_ALU_R: begin
            ALUSrcA = 1'b1;
            ALUSrcB = 2'b00; 
            case (IR[5:0])
               6'b100000, // add , addu
               6'b100001: aluOp = `ADD;
               6'b100010, // sub , subu
               6'b100011: aluOp = `SUB;
               6'b100100: aluOp = `AND; // and
               6'b100101: aluOp = `OR; // or
               6'b100110: aluOp = `XOR; // xor
               6'b100111: aluOp = `NOR; // nor
               6'b101010: aluOp = `SLT; // slt
               6'b101011: aluOp = `SLTU; // sltu
            endcase
            RegDst = 2'b01;
            MemtoReg = 1'b0;
            MARwrt = 1'b0;
            RegWrite = 1'b1;
            PrepareFetch;
         end

         EX_JUMP_R: begin
            JumpControl = 1'b0;
            PCwrt = 1'b1;
            jump = 1'b1;
            if (IR[2:0] == 3'b001) begin // jalr 
               RegDst = 2'b10;
               InputDataControl = 3'b100;
               MemtoReg = 1'b1;
               RegWrite = 1'b1;
            end
            nxt_state = EX_JUMP_R2;
         end

         EX_JUMP_R2: begin
            PrepareFetch;
         end

         EX_MULT_R1: begin
            MultControl = 1'b1;
            nxt_state = EX_MULT_R2;
         end
         
         EX_MULT_R2: begin
            if(MultReady) begin
               HIwrt = 1'b1;
               LOwrt = 1'b1;
               PrepareFetch;
            end
            else
               nxt_state = EX_MULT_R2;
         end
         
         EX_ALU_I: begin
            ALUSrcA = 1'b1;
            ALUSrcB = 2'b10; 
            case (IR[31:26])
               6'b001_000: begin
                  aluOp = `ADD; // addi
                  SgnExt = 1'b1;
               end
               6'b001_001: begin
                  aluOp = `ADD; // addui
                  SgnExt = 1'b0;
               end
               6'b001_010: begin
                  aluOp = `SLT; // slti
                  SgnExt = 1'b1;
               end
               6'b001_011: begin
                  aluOp = `SLTU; // sltiu
                  SgnExt = 1'b0;
               end
               6'b001_100:begin
                  aluOp = `AND; // andi
                  SgnExt = 1'b0;
               end
               6'b001_101:begin
                  aluOp = `OR; // ori
                  SgnExt = 1'b0;
               end
               6'b001_110:begin
                  aluOp = `XOR; // xori
                  SgnExt = 1'b0; 
               end
            endcase
            RegDst = 2'b00;
            MemtoReg = 1'b0;
            MARwrt = 1'b0 ;
            Datawrt = 1'b0;
            RegWrite = 1'b1;
            PrepareFetch;
         end

         EX_LUI: begin
            MemtoReg = 1'b1;  
            RegDst = 2'b00;
            RegWrite = 1'b1;
            InputDataControl = 3'b001; 
            PrepareFetch;
         end

         EX_LW_1: begin
            MARwrt = 1'b1;
            ALUSrcA = 1'b1;
            ALUSrcB = 2'b10; 
            SgnExt = 1'b1;
            aluOp = `ADD;
            IorD = 1'b1;
            setMemoryReadEnable = 1'b1;
            nxt_state = EX_LW_2;
         end

         EX_LW_2:
            nxt_state = EX_LW_3;

         EX_LW_3:
            nxt_state = EX_LW_4;

         EX_LW_4: begin
            clrMemoryReadEnable = 1'b1;
            Datawrt = 1'b1;
            nxt_state = EX_LW_5;
         end

         EX_LW_5: begin
            RegDst = 2'b00;
            RegWrite = 1'b1;
            MemtoReg = 1'b1;
            PrepareFetch;
         end

         EX_SW_1: begin
            IorD = 1'b1;
            MARwrt = 1'b1;
            ALUSrcA = 1'b1;
            ALUSrcB = 2'b10; 
            aluOp = `ADD;
            SgnExt = 1'b1;
            setMemoryWriteEnable = 1'b1;
            nxt_state = EX_SW_2;
         end

         EX_SW_2: begin
            clrMemoryWriteEnable = 1'b1;
            nxt_state = EX_SW_3;
         end

         EX_SW_3:
            PrepareFetch;

         EX_BEQ_1: begin
            aluOp = `SUB;
            ALUSrcA = 1'b1 ;
            ALUSrcB = 2'b00;

            if(aluZero)
               nxt_state = EX_BRA_2;
            else
               PrepareFetch;
         end

         EX_BNE_1: begin
            aluOp = `SUB;
            ALUSrcA = 1'b1 ;
            ALUSrcB = 2'b00;

            if(!aluZero)
               nxt_state = EX_BRA_2;
            else
               PrepareFetch;
         end

         EX_BRA_2: begin
            SgnExt = 1'b1;
            ALUSrcA = 1'b0;
            ALUSrcB = 2'b11 ;
            aluOp = `ADD;
            PCwrt = 1'b1;
            IorD = 1'b1;
            MARwrt = 1'b1;
            setMemoryReadEnable = 1'b1;
            nxt_state = FETCH1;
         end

         EX_JUMP: begin
            PCwrt = 1'b1;
            JumpControl = 1'b1;
            jump = 1'b1;
            nxt_state = EX_JUMP_2;
         end
         EX_JUMP_2: begin
            PrepareFetch;
         end

         EX_JLINK: begin
            RegDst = 2'b10;
            InputDataControl = 3'b100;
            MemtoReg = 1'b1;
            RegWrite = 1'b1;
            nxt_state = EX_JUMP;
         end


         EX_MOVE: begin
            RegWrite = 1'b1;
            RegDst = 2'b01;
            case (IR[5:0])
               6'b010_000: // mfhi
                  InputDataControl = 3'b010;
               6'b010_010: // mflo
                  InputDataControl = 3'b011;
            endcase
            MemtoReg = 1'b1;
            PrepareFetch;
         end

      endcase

   end

endmodule

//==============================================================================

module my_alu(
   input [2:0] Op,
   input [31:0] A,
   input [31:0] B,

   output [31:0] X,
   output        Z
);

   wire sub = Op != `ADD;

   wire [31:0] bb = sub ? ~B : B;

   wire [32:0] sum = A + bb + sub;

   wire sltu = ! sum[32];

   wire v = sub ? 
        ( A[31] != B[31] && A[31] != sum[31] )
      : ( A[31] == B[31] && A[31] != sum[31] );

   wire slt = v ^ sum[31];

   reg [31:0] x;

   always @( * )
      case( Op )
         `ADD : x = sum;
         `SUB : x = sum;
         `SLT : x = slt;
         `SLTU: x = sltu;
         `AND : x =   A & B;
         `OR  : x =   A | B;
         `NOR : x = ~(A | B);
         `XOR : x =   A ^ B;
         default : x = 32'hxxxxxxxx;
      endcase

   assign #2 X = x;
   assign #2 Z = x == 32'h00000000;

endmodule

//==============================================================================

module reg_file(
   input clk,
   input write,
   input [4:0] WR,
   input [31:0] WD,
   input [4:0] RR1,
   input [4:0] RR2,
   output [31:0] RD1,
   output [31:0] RD2
);

   reg [31:0] rf_data [0:31];

   assign #2 RD1 = rf_data[ RR1 ];
   assign #2 RD2 = rf_data[ RR2 ];   

   always @( posedge clk ) begin
      if ( write )
         rf_data[ WR ] <= WD;

      rf_data[0] <= 32'h00000000;
   end

endmodule

//==============================================================================

module multiplier(
//-----------------------Port directions and deceleration
   input clk,  
   input start,
   input [31:0] A, 
   input [31:0] B, 
   output[31:0] hi,
   output[31:0] lo,
   output ready
    );

//------------------------------------------------------

//----------------------------------- register deceleration
reg [31:0]  Multiplier;
reg [65:0] PartialProduct;
reg [5:0]  counter;
reg omittedBit;
//-------------------------------------------------------

//------------------------------------- wire deceleration
wire product_write_enable;
wire [33:0] adder_output;
//---------------------------------------------------------

//-------------------------------------- combinational logic
assign #2.3 adder_output = // if
PartialProduct[1]?
PartialProduct[0]&omittedBit?{{2{PartialProduct[65]}},PartialProduct[65:34]}:
PartialProduct[0]^omittedBit?{{2{PartialProduct[65]}},PartialProduct[65:34]} - Multiplier:{{2{PartialProduct[65]}},PartialProduct[65:34]} - {Multiplier,1'b0} :
PartialProduct[0]&omittedBit?{{2{PartialProduct[65]}},PartialProduct[65:34]} + {Multiplier,1'b0}:
PartialProduct[0]^omittedBit?{{2{PartialProduct[65]}},PartialProduct[65:34]} + Multiplier:{{2{PartialProduct[65]}},PartialProduct[65:34]};

assign #0.1 ready = counter[5];
assign hi = PartialProduct[63:32];
assign lo = PartialProduct[31:0];

always @ (posedge clk)

   if(start) begin
      counter <= #0.1 6'h0F ;
      Multiplier <= #0.1 A;
      PartialProduct <= #0.1 {34'h0, B};
      omittedBit <= #0.1 1'b0;
   end

   else if(! ready) begin
         counter <= #0.1 counter + 1;
         PartialProduct <= #0.1 {adder_output,PartialProduct[33:2]};
         omittedBit <= #0.1 PartialProduct[1];
   end   

endmodule

