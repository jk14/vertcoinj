
package fr.cryptohash;

import javax.tools.JavaCompiler;
import java.lang.reflect.Array;
import java.math.BigInteger;
import java.nio.ByteOrder;
import java.util.Arrays;
import java.nio.ByteBuffer;

public class Lyra2 {

    public static int to1dIndex(int row, int col, int cols) {
        return cols * row + col;
    }

    public static long byteSize2longSize(long byteSize) {
        return (long) Math.ceil((double) byteSize / (double) Sponge.LONG_SIZE_IN_BYTES);
    }

    public static long byte2long(byte[] bytes, int offset) {
        return ByteBuffer.wrap(bytes).order(ByteOrder.LITTLE_ENDIAN).getLong(offset);
    }

    public static void copyByteArray2longArray(byte[] bytes, long[] output, int output_pos) {
        int i = output_pos;

        for (int j = Sponge.ANY_ARRAY_START; j + Sponge.LONG_SIZE_IN_BYTES <= bytes.length && i <= output.length; j += Sponge.LONG_SIZE_IN_BYTES, ++i) {
            output[i] = byte2long(bytes, j);
        }
    }

    public static int putLongToByteArray(byte[] array, int offset, long value)
    {
        ByteBuffer buffer = ByteBuffer.allocate(Sponge.LONG_SIZE_IN_BYTES).order(ByteOrder.LITTLE_ENDIAN);
        buffer.putLong(value);
        byte[] bytes = buffer.array();
        for (int j = 0; j < Sponge.LONG_SIZE_IN_BYTES && offset < array.length; ++offset, ++j) {
            array[offset] = bytes[j];
        }
        return offset;
    }

    public static int calcBlocksInput(byte[] user_password, byte[] salt)
    {
        final int args_to_write = 6; //output_key_len, password_len, salt_len, time_cost, memory_matrix_rows & cols
        final int size_for_basil = args_to_write * Sponge.LONG_SIZE_IN_BYTES;
        final int size_for_password_and_salt = user_password.length + salt.length;
        return (size_for_password_and_salt + size_for_basil) / Sponge.BLOCK_LEN_BLAKE2_SAFE_BYTES + 1;
    }

    public static void padding(int output_key_len, long time_cost, byte[] user_password, byte[] salt, int memory_matrix_rows, int memory_matrix_columns, long[] wholeMatrix)
    {
        //============= Getting the password + salt + basil padded with 10*1 ===============//
        //OBS.:The memory matrix will temporarily hold the password: not for saving memory,
        //but this ensures that the password copied locally will be overwritten as soon as possible

        //First merge all padding elements into one byte array
        final int blocks_input = calcBlocksInput(user_password, salt);
        byte[] padding_bytes = new byte[blocks_input * Sponge.BLOCK_LEN_BLAKE2_SAFE_BYTES];

        //Copy password to padding bytes
        int i = Sponge.ANY_ARRAY_START;
        for ( ; i < user_password.length; ++i) {
            padding_bytes[i] = user_password[i];
        }
        //Copy salt to padding bytes after the password
        for ( ; i < user_password.length + salt.length; ++i) {
            padding_bytes[i] = salt[i - user_password.length];
        }

        //Copy the basil - args one by another
        i = putLongToByteArray(padding_bytes, i, output_key_len);
        i = putLongToByteArray(padding_bytes, i, user_password.length);
        i = putLongToByteArray(padding_bytes, i, salt.length);
        i = putLongToByteArray(padding_bytes, i, time_cost);
        i = putLongToByteArray(padding_bytes, i, memory_matrix_rows);
        i = putLongToByteArray(padding_bytes, i, memory_matrix_columns);
        i = putLongToByteArray(padding_bytes, i, 128);
        final int modifier_index = padding_bytes.length - 1;
        padding_bytes[modifier_index] ^= (byte) 1;
        copyByteArray2longArray(padding_bytes, wholeMatrix, Sponge.ANY_ARRAY_START);
    }

    /**
     * Executes Lyra2 based on the G function from Blake2b. This version supports salts and passwords
     * whose combined length is smaller than the size of the memory matrix, (i.e., (memory_matrix_rows x memory_matrix_columns x b) bits,
     * where "b" is the underlying sponge's bitrate). In this implementation, the "basil" is composed by all
     * integer parameters (treated as type "unsigned int") in the order they are provided, plus the value
     * of memory_matrix_columns, (i.e., basil = output_key.length || user_password.length || salt.length || time_cost || memory_matrix_rows || memory_matrix_columns).
     *
     * @param output_key The derived key to be output by the algorithm
     * @param user_password User password
     * @param salt Salt
     * @param time_cost Parameter to determine the processing time (T)
     * @param memory_matrix_rows Number or rows of the memory matrix (R)
     * @param memory_matrix_columns Number of columns of the memory matrix (C)
     *
     * @return 0 if the key is generated correctly; -1 if there is an error (usually due to lack of memory for allocation)
     */

    public static BigInteger long2unsigned(long v)
    {
        ByteBuffer buffer = ByteBuffer.allocate(Sponge.LONG_SIZE_IN_BYTES);
        buffer.putLong(v);
        byte[] bytes = buffer.array();
        byte[] big_bytes = new byte[bytes.length * 2];
        for (int i = 0; i < bytes.length; ++i) {
            big_bytes[bytes.length + i] = bytes[i];
        }
        return new BigInteger(big_bytes);
    }

    public static BigInteger overflowUint64_t(BigInteger v)
    {
        BigInteger UINT64_MAX = new BigInteger("18446744073709551615");
        if (v.compareTo(UINT64_MAX) == 1) //Greater then MAX
        {
            v = v.mod((new BigInteger("18446744073709551616")));
        }
        return v;
    }

    public static long unsignedAdd(long v1, long v2)
    {
        BigInteger a = Lyra2.long2unsigned(v1);
        BigInteger b = Lyra2.long2unsigned(v2);
        a = a.add(b);
        a = Lyra2.overflowUint64_t(a);
        return a.longValue();
    }

    public static int LYRA2(byte[] output_key,
                            byte[] user_password,
                            byte[] salt,
                            long time_cost, int memory_matrix_rows, int memory_matrix_columns) {

        //============================= Basic variables ============================//
        int row = 2; //index of row to be processed
        int prev = 1; //index of prev (last row ever computed/modified)
        int rowa = 0; //index of row* (a previous row, deterministically picked during Setup and randomly picked while Wandering)
        int tau; //Time Loop iterator
        int step = 1; //Visitation step (used during Setup and Wandering phases)
        int window = 2; //Visitation window (used to define which rows can be revisited during Setup)
        int gap = 1; //Modifier to the step, assuming the values 1 or -1
        int i; //auxiliary iteration counter
        //==========================================================================/

        //========== Initializing the Memory Matrix and pointers to it =============//
        //Tries to allocate enough space for the whole memory matrix


        final int ROW_LEN_INT64 = Sponge.BLOCK_LEN_INT64 * memory_matrix_columns;

        long[] wholeMatrix = new long[memory_matrix_rows * ROW_LEN_INT64];
        padding(output_key.length, time_cost, user_password, salt, memory_matrix_rows, memory_matrix_columns, wholeMatrix);
        //======================= Initializing the Sponge State ====================//
        //Sponge state: 16 long, BLOCK_LEN_INT64 words of them for the bitrate (b) and the remainder for the capacity (c)
        long[] state = new long[16];
        Sponge.initState(state);
        //==========================================================================/

        //================================ Setup Phase =============================//
        //Absorbing salt, password and basil: this is the only place in which the block length is hard-coded to 512 bits
        int dest_pos = Sponge.ANY_ARRAY_START;
        final int blocks_input = ((user_password.length + salt.length + 6 * Sponge.LONG_SIZE_IN_BYTES) / Sponge.BLOCK_LEN_BLAKE2_SAFE_BYTES) + 1;
        for (i = 0; i < blocks_input; i++) {
            Sponge.absorbBlockBlake2Safe(state, wholeMatrix, dest_pos); //absorbs each block of pad(user_password || salt || basil)
            dest_pos += Sponge.BLOCK_LEN_BLAKE2_SAFE_INT64; //goes to next block of pad(user_password || salt || basil)
        }

        //Initializes M[0] and M[1]
        Sponge.reducedSqueezeRow0(state, wholeMatrix, memory_matrix_columns); //The locally copied password is most likely overwritten here

        final int first_column = 0;
        Sponge.reducedDuplexRow1(state,
                wholeMatrix,
                to1dIndex(rowa, first_column, ROW_LEN_INT64),
                to1dIndex(prev, first_column, ROW_LEN_INT64),
                memory_matrix_columns);


        do {
            //M[row] = rand; //M[row*] = M[row*] XOR rotW(rand)
            Sponge.reducedDuplexRowSetup(state,
                    wholeMatrix,
                    to1dIndex(prev, first_column, ROW_LEN_INT64),
                    to1dIndex(rowa, first_column, ROW_LEN_INT64),
                    to1dIndex(row, first_column, ROW_LEN_INT64),
                    memory_matrix_columns);

            //updates the value of row* (deterministically picked during Setup))
            rowa = (rowa + step) & (window - 1);
            //update prev: it now points to the last row ever computed
            prev = row;
            //updates row: goes to the next row to be computed
            row++;

            //Checks if all rows in the window where visited.
            if (rowa == 0) {
                step = window + gap; //changes the step: approximately doubles its value
                window *= 2; //doubles the size of the re-visitation window
                gap = -gap; //inverts the modifier to the step
            }

        } while (row < memory_matrix_rows);
        //==========================================================================/

        //============================ Wandering Phase =============================//
        row = 0; //Resets the visitation to the first row of the memory matrix
        for (tau = 1; tau <= time_cost; tau++) {
            //Step is approximately half the number of all rows of the memory matrix for an odd tau; otherwise, it is -1
            BigInteger bigstep;
            if (tau % 2 == 0) {
                bigstep = new BigInteger("18446744073709551615");
            } else {
                bigstep = new BigInteger(Integer.toString(memory_matrix_rows / 2 - 1));
            }
            do {
                //Selects a pseudorandom index row*
                //------------------------------------------------------------------------------------------
                //rowa = ((unsigned int)state[0]) & (memory_matrix_rows-1);	//(USE THIS IF memory_matrix_rows IS A POWER OF 2)
                //rowa = Math.abs((byte) state[0] % memory_matrix_rows);
                BigInteger unsigned_state = long2unsigned(state[0]);
                BigInteger modulo = unsigned_state.mod(new BigInteger(Integer.toString(memory_matrix_rows)));
                rowa = modulo.intValue();
                //------------------------------------------------------------------------------------------
                //Performs a reduced-round duplexing operation over M[row*] XOR M[prev], updating both M[row*] and M[row]
                Sponge.reducedDuplexRow(state,
                        wholeMatrix,
                        to1dIndex(prev, first_column, ROW_LEN_INT64),
                        to1dIndex(rowa, first_column, ROW_LEN_INT64),
                        to1dIndex(row, first_column, ROW_LEN_INT64),
                        memory_matrix_columns);

                //update prev: it now points to the last row ever computed
                prev = row;

                //updates row: goes to the next row to be computed
                //------------------------------------------------------------------------------------------
                //row = (row + step) & (memory_matrix_rows-1);	//(USE THIS IF memory_matrix_rows IS A POWER OF 2)
                //(row + step) % memory_matrix_rows; //(USE THIS FOR THE "GENERIC" CASE)
                row = (int) bigstep.add(new BigInteger(Integer.toString(row))).mod(new BigInteger(Integer.toString(memory_matrix_rows))).longValue();
                //------------------------------------------------------------------------------------------

            } while (row != 0);
        }
        //==========================================================================/

        //============================ Wrap-up Phase ===============================//
        //Absorbs the last block of the memory matrix
        Sponge.absorbBlock(state, wholeMatrix, to1dIndex(rowa, first_column, ROW_LEN_INT64));

        //Squeezes the key
        Sponge.squeeze(state, output_key, output_key.length);
        //==========================================================================/

        return 0;
    }

}
