
package fr.cryptohash;

import java.math.BigInteger;
import java.nio.ByteBuffer;
import java.nio.ByteOrder;
import java.util.Arrays;

class Sponge {
    public static int LONG_SIZE_IN_BYTES = Long.SIZE / Byte.SIZE;
    public static int BLOCK_LEN_INT64 = 12; //12 longs
    public static int BLOCK_LEN_BYTES = 12 * 8; //same as above, in bytes
    public static int BLOCK_LEN_BLAKE2_SAFE_INT64 = 8; // 8 longs
    public static int BLOCK_LEN_BLAKE2_SAFE_BYTES = (BLOCK_LEN_BLAKE2_SAFE_INT64 * 8); //same as above, in bytes
    public static int ANY_ARRAY_START = 0;

    /*Blake2b IV Array*/
    public static long[] blake2b_IV = {
            0x6a09e667f3bcc908L, 0xbb67ae8584caa73bL,
            0x3c6ef372fe94f82bL, 0xa54ff53a5f1d36f1L,
            0x510e527fade682d1L, 0x9b05688c2b3e6c1fL,
            0x1f83d9abfb41bd6bL, 0x5be0cd19137e2179L
    };

    /*Blake2b's rotation*/
    public static long rotr64(long w, int c) {
        return (w >>> c) | (w << (64 - c));
    }

    /*Blake2b's G function*/
    public static void G_function(long r, long i, long[] v, int[] abcd)
    {
        final int a = abcd[0];
        final int b = abcd[1];
        final int c = abcd[2];
        final int d = abcd[3];

        v[a] = Lyra2.unsignedAdd(v[a], v[b]);
        v[d] = rotr64(v[d] ^ v[a], 32);
        v[c] = Lyra2.unsignedAdd(v[c], v[d]);
        v[b] = rotr64(v[b] ^ v[c], 24);
        v[a] = Lyra2.unsignedAdd(v[a], v[b]);
        v[d] = rotr64(v[d] ^ v[a], 16);
        v[c] = Lyra2.unsignedAdd(v[c], v[d]);
        v[b] = rotr64(v[b] ^ v[c], 63);
    }

    /*One Round of the Blake2b's compression function*/
    public static void round_lyra(long r, long[] v) {
        G_function(r, 0, v, new int[]{ 0, 4, 8, 12});
        G_function(r, 1, v, new int[]{ 1, 5, 9, 13});
        G_function(r, 2, v, new int[]{ 2, 6, 10, 14});
        G_function(r, 3, v, new int[]{ 3, 7, 11, 15});
        G_function(r, 4, v, new int[]{ 0, 5, 10, 15});
        G_function(r, 5, v, new int[]{ 1, 6, 11, 12});
        G_function(r, 6, v, new int[]{ 2, 7, 8, 13});
        G_function(r, 7, v, new int[]{ 3, 4, 9, 14});
    }


    /**
     * Initializes the Sponge State. The first 512 bits are set to zeros and the remainder
     * receive Blake2b's IV as per Blake2b's specification. <b>Note:</b> Even though sponges
     * typically have their internal state initialized with zeros, Blake2b's G function
     * has a fixed point: if the internal state and message are both filled with zeros. the
     * resulting permutation will always be a block filled with zeros; this happens because
     * Blake2b does not use the constants originally employed in Blake2 inside its G function,
     * relying on the IV for avoiding possible fixed points.
     *
     * @param state         The 1024-bit array to be initialized
     */
    public static void initState(long[/*16*/] state) {
        //Fill first 512 bits to zero (8 * long = 64 bytes)
        for (int i = 0; i < BLOCK_LEN_BLAKE2_SAFE_INT64; ++i) {
            state[i] = 0;
        }
        //Remainder BLOCK_LEN_BLAKE2_SAFE_BYTES are reserved to the IV
        state[8] = blake2b_IV[0];
        state[9] = blake2b_IV[1];
        state[10] = blake2b_IV[2];
        state[11] = blake2b_IV[3];
        state[12] = blake2b_IV[4];
        state[13] = blake2b_IV[5];
        state[14] = blake2b_IV[6];
        state[15] = blake2b_IV[7];
    }

    /**
     * Execute Blake2b's G function, with all 12 rounds.
     *
     * @param v     A 1024-bit (16 long) array to be processed by Blake2b's G function
     */
    public static void blake2bLyra(long[] v) {
        for (int i = 0; i < BLOCK_LEN_INT64; ++i) {
            round_lyra(i, v);
        }
    }

    /**
     * Executes a reduced version of Blake2b's G function with only one round
     * @param v     A 1024-bit (16 long) array to be processed by Blake2b's G function
     */
    public static void reducedBlake2bLyra(long[] v) {
        round_lyra(0, v);
    }

    public static void toByte(long[] state, byte[] state_bytes) {
        for (int i = 0; i < state.length; ++i) {
            byte[] bytes = ByteBuffer.allocate(LONG_SIZE_IN_BYTES).order(ByteOrder.LITTLE_ENDIAN).putLong(state[i]).array();
            for (int j = 0; j < LONG_SIZE_IN_BYTES; ++j) {
                state_bytes[i * LONG_SIZE_IN_BYTES + j] = bytes[j];
            }
        }
    }


    /**
     * Performs a squeeze operation, using Blake2b's G function as the
     * internal permutation
     *
     * @param state      The current state of the sponge
     * @param out        Array that will receive the data squeezed
     * @param len        The number of bytes to be squeezed into the "out" array
     */
    public static void squeeze(long[] state, byte[] out, int len) {
        byte[] state_bytes = new byte[state.length * LONG_SIZE_IN_BYTES];
        toByte(state, state_bytes);

        int fullBlocks = len / BLOCK_LEN_BYTES;
        int out_itr = ANY_ARRAY_START;
        int state_itr = ANY_ARRAY_START;

        //Squeezes full blocks
        for (int i = 0; i < fullBlocks; ++i) {
            System.arraycopy(state_bytes, state_itr, out, out_itr, BLOCK_LEN_BYTES);
            blake2bLyra(state);
            toByte(state, state_bytes);
            out_itr += BLOCK_LEN_BYTES;
        }

        //Squeezes remaining bytes
        for (int i = 0; out_itr + i < out.length; ++i) {
            out[out_itr + i] = state_bytes[i];
        }
    }

    /**
     * Performs an absorb operation for a single block (BLOCK_LEN_INT64 words
     * of type long), using Blake2b's G function as the internal permutation
     *
     * @param state The current state of the sponge
     * @param in    The block to be absorbed (BLOCK_LEN_INT64 words)
     */
    public static void absorbBlock(long[] state, long[] in, int offset) {
        //XORs the first BLOCK_LEN_INT64 words of "in" with the current state
        for (int i = 0; i < BLOCK_LEN_INT64; ++i) {
            state[i] ^= in[offset + i];
        }

        //Applies the transformation f to the sponge's state
        blake2bLyra(state);
    }

    /**
     * Performs an absorb operation for a single block (BLOCK_LEN_BLAKE2_SAFE_INT64
     * words of type long), using Blake2b's G function as the internal permutation
     *
     * @param state The current state of the sponge
     * @param in    The block to be absorbed (BLOCK_LEN_BLAKE2_SAFE_INT64 words)
     */
    public static void absorbBlockBlake2Safe(long[] state, long[] in, int in_offset) {
        //XORs the first BLOCK_LEN_BLAKE2_SAFE_INT64 words of "in" with the current state
        for (int i = 0; i < BLOCK_LEN_BLAKE2_SAFE_INT64; ++i) {
            state[i] ^= in[in_offset + i];
        }

        //Applies the transformation f to the sponge's state
        blake2bLyra(state);
    }

    /**
     * Performs a reduced squeeze operation for a single row, from the highest to
     * the lowest index, using the reduced-round Blake2b's G function as the
     * internal permutation
     *
     * @param state     The current state of the sponge
     * @param row_out    Row to receive the data squeezed
     */
    public static void reducedSqueezeRow0(long[] state, long[] row_out, long n_cols) {
        int row_out_itr = (int)(ANY_ARRAY_START + (n_cols - 1) * BLOCK_LEN_INT64); //In Lyra2: pointer to M[0][C-1]
        //M[row][C-1-col] = H.reduced_squeeze()
        for (int i = 0; i < n_cols; i++) {
            System.arraycopy(state, ANY_ARRAY_START, row_out, row_out_itr, BLOCK_LEN_INT64);

            //Goes to next block (column) that will receive the squeezed data
            row_out_itr -= BLOCK_LEN_INT64;

            //Applies the reduced-round transformation f to the sponge's state
            reducedBlake2bLyra(state);
        }
    }

    /**
     * Performs a reduced duplex operation for a single row, from the highest to
     * the lowest index, using the reduced-round Blake2b's G function as the
     * internal permutation
     *
     * @param state		The current state of the sponge
     * @param row_in		Row to feed the sponge
     * @param row_out	Row to receive the sponge's output
     */
    public static void reducedDuplexRow1(long[] state, long[] matrix, int row_in, int row_out, long n_cols) {
        int row_in_itr = row_in;				//In Lyra2: pointer to prev
        int row_out_itr = (int)(row_out + (n_cols - 1) * BLOCK_LEN_INT64); //In Lyra2: pointer to row
        for (int i = 0; i < n_cols; i++) {

            //Absorbing "M[prev][col]"
            for (int p = 0; p < BLOCK_LEN_INT64; ++p) {
                state[p] ^= matrix[row_in_itr + p];
            }

            //Applies the reduced-round transformation f to the sponge's state
            reducedBlake2bLyra(state);

            //M[row][C-1-col] = M[prev][col] XOR rand
            for (int p = 0; p < BLOCK_LEN_INT64; ++p) {
                matrix[row_out_itr + p] = matrix[row_in_itr + p] ^ state[p];
            }

            //Input: next column (i.e., next block in sequence)
            row_in_itr += BLOCK_LEN_INT64;
            //Output: goes to previous column
            row_out_itr -= BLOCK_LEN_INT64;
        }
    }

    /**
     * Performs a duplexing operation over "M[row_in_out][col] [+] M[row_in][col]" (i.e.,
     * the wordwise addition of two columns, ignoring carries between words). The
     * output of this operation, "rand", is then used to make
     * "M[row_out][(N_COLS-1)-col] = M[row_in][col] XOR rand" and
     * "M[row_in_out][col] =  M[row_in_out][col] XOR rotW(rand)", where rotW is a 64-bit
     * rotation to the left and N_COLS is a system parameter.
     *
     * @param state          The current state of the sponge
     * @param row_in          Row used only as input
     * @param row_in_out       Row used as input and to receive output after rotation
     * @param row_out         Row receiving the output
     *
     */
    public static void reducedDuplexRowSetup(long[] state, long[] matrix, int row_in, int row_in_out, int row_out, long n_cols) {
        int row_in_itr = row_in;				//In Lyra2: pointer to prev
        int row_in_out_itr = row_in_out;				//In Lyra2: pointer to row*
        int row_out_itr = (int)(row_out + (n_cols - 1) * BLOCK_LEN_INT64); //In Lyra2: pointer to row

        //Absorbing "M[prev] [+] M[row*]"
        for (int i = 0; i < n_cols; i++) {

            for (int p = 0; p < BLOCK_LEN_INT64; ++p) {
                state[p] ^= (matrix[row_in_itr + p] + matrix[row_in_out_itr + p]);
            }

            //Applies the reduced-round transformation f to the sponge's state
            reducedBlake2bLyra(state);

            //M[row][col] = M[prev][col] XOR rand
            for (int p = 0; p < BLOCK_LEN_INT64; ++p) {
                matrix[row_out_itr + p] = (matrix[row_in_itr + p] ^ state[p]);
            }

            //M[row*][col] = M[row*][col] XOR rotW(rand)
            for (int p = 0; p < BLOCK_LEN_INT64; ++p) {
                matrix[row_in_out_itr + p] ^= state[(11 + p) % BLOCK_LEN_INT64];
            }

            //Inputs: next column (i.e., next block in sequence)
            row_in_out_itr += BLOCK_LEN_INT64;
            row_in_itr += BLOCK_LEN_INT64;
            //Output: goes to previous column
            row_out_itr -= BLOCK_LEN_INT64;
        }
    }

    /**
     * Performs a duplexing operation over "M[row_in_out][col] [+] M[row_in][col]" (i.e.,
     * the wordwise addition of two columns, ignoring carries between words). The
     * output of this operation, "rand", is then used to make
     * "M[row_out][col] = M[row_out][col] XOR rand" and
     * "M[row_in_out][col] =  M[row_in_out][col] XOR rotW(rand)", where rotW is a 64-bit
     * rotation to the left.
     *
     * @param state          The current state of the sponge
     * @param row_in          Row used only as input
     * @param row_in_out       Row used as input and to receive output after rotation
     * @param row_out         Row receiving the output
     *
     */
    public static void reducedDuplexRow(long[] state, long[] matrix, int row_in, int row_in_out, int row_out, long nCols) {
        int row_in_out_itr = row_in_out; //In Lyra2: pointer to row*
        int row_in_itr = row_in; //In Lyra2: pointer to prev
        int row_out_itr = row_out; //In Lyra2: pointer to row

        for (int i = 0; i < nCols; i++) {

            //Absorbing "M[prev] [+] M[row*]"
            for (int p = 0; p < BLOCK_LEN_INT64; ++p) {
                state[p] ^= matrix[row_in_itr + p] + matrix[row_in_out_itr + p];
            }

            //Applies the reduced-round transformation f to the sponge's state
            reducedBlake2bLyra(state);

            //M[row_out][col] = M[row_out][col] XOR rand
            for (int p = 0; p < BLOCK_LEN_INT64; ++p) {
                matrix[row_out_itr + p] ^= state[p];
            }

            //M[row_in_out][col] = M[row_in_out][col] XOR rotW(rand)
            for (int p = 0; p < BLOCK_LEN_INT64; ++p) {
                matrix[row_in_out_itr + p] ^= state[(11 + p) % BLOCK_LEN_INT64];
            }

            //Goes to next block
            row_out_itr += BLOCK_LEN_INT64;
            row_in_out_itr += BLOCK_LEN_INT64;
            row_in_itr += BLOCK_LEN_INT64;
        }
    }
}
