#include <iostream>
#include <optional>

#include <boost/asio.hpp>

#include "vdf.h"


using namespace std;


int gcd_base_bits = 50;
int gcd_128_max_iter = 3;


struct vdf_result {
    // TODO?: add D, T
    form y;
    form p;
};

struct bluebox_request {
    integer discriminant;
    uint64_t iterations;
};


void repeated_square_1weso(const integer& D, uint64_t T, WesolowskiCallback* weso) {
    vdf_original vdfo;
    integer L = root(-D, 4);
    form x = form::generator(D);

    uint64_t num_iterations = 0;
    while (num_iterations <= T) {
        uint64 batch_size = checkpoint_interval;

        square_state_type square_state;
        square_state.pairindex = 0;

        // Overall throughput for blueboxing significantly increases if we run
        // one single-threaded worker per CPU (hyper-)thread, instead of one
        // dual-threaded worker per every two CPU (hyper-)threads.
        uint64 actual_iterations = repeated_square_fast_single_thread(square_state, x, D, L, num_iterations, batch_size, weso);
        if (actual_iterations == ~uint64(0)) {
            // Corruption; f is unchanged. Do the entire batch with the slow
            // algorithm.
            repeated_square_original(vdfo, x, D, L, num_iterations, batch_size, weso);
            actual_iterations = batch_size;
        } else if (actual_iterations < batch_size) {
            // The fast algorithm terminated prematurely for whatever reason. f
            // is still valid. It might terminate prematurely again (e.g. gcd
            // quotient too large), so do one iteration of the slow algorithm.
            // This will also reduce f if the fast algorithm terminated because
            // it was too big.
            repeated_square_original(vdfo, x, D, L, num_iterations + actual_iterations, 1, weso);
            actual_iterations += 1;
        }
        num_iterations += actual_iterations;
    }
}

form prove_1weso(integer D, uint64_t T, form y, form* intermediates) {
    form x = form::generator(D);

    // OneWesolowskiProver(Segment(0, T, x, y), D, intermediates, stopped)
    uint32_t k;
    uint32_t l;
    if (T >= (1 << 16)) {
        ApproximateParameters(T, k, l);
    } else {
        k = 10;
        l = 1;
    }

    // GenerateProof()
    uint64_t k1 = k / 2;
    uint64_t k0 = k - k1;

    PulmarkReducer reducer;

    integer B = GetB(D, x, y);
    integer L = root(-D, 4);
    form id = form::identity(D);
    form p = id;

    for (int64_t j = l - 1; j >= 0; j--) {
        p = FastPowFormNucomp(p, D, integer(1 << k), L, reducer);

        vector<form> ys((1 << k));
        for (uint64_t i = 0; i < (1 << k); i++) {
            ys[i] = id;
        }

        uint64_t limit = T / (k * l);
        if (T % (k * l)) {
            limit++;
        }

        for (uint64_t i = 0; i < limit; i++) {
            if (T >= k * (i * l + j + 1)) {
                // uint64_t b = GetBlock(i*l + j, k, T, B);
                integer res = FastPow(2, T - k * (i*l + j + 1), B);
                mpz_mul_2exp(res.impl, res.impl, k);
                res = res / B;
                auto res_vector = res.to_vector();  // @@ smells
                uint64_t b = res_vector.empty() ? 0 : res_vector[0];

                nucomp_form(ys[b], ys[b], intermediates[i], D, L);
            }
        }

        for (uint64_t b1 = 0; b1 < (1 << k1); b1++) {
            form z = id;
            for (uint64_t b0 = 0; b0 < (1 << k0); b0++) {
                nucomp_form(z, z, ys[b1 * (1 << k0) + b0], D, L);
            }
            z = FastPowFormNucomp(z, D, integer(b1 * (1 << k0)), L, reducer);
            nucomp_form(p, p, z, D, L);
        }

        for (uint64_t b0 = 0; b0 < (1 << k0); b0++) {
            form z = id;
            for (uint64_t b1 = 0; b1 < (1 << k1); b1++) {
                nucomp_form(z, z, ys[b1 * (1 << k0) + b0], D, L);
            }
            z = FastPowFormNucomp(z, D, integer(b0), L, reducer);
            nucomp_form(p, p, z, D, L);
        }
    }
    reducer.reduce(p);

    return p;
}

vdf_result vdf_1weso(integer& D, uint64_t T) {
    cout << "[vdf] Computing repeated square x^2^" << T << "." << endl << flush;

    form x = form::generator(D);
    cout << "[vdf] Base: x.c=" << x.c.impl << endl;
    OneWesolowskiCallback weso_cb(D, x, T);
    auto t0 = chrono::high_resolution_clock::now();
    repeated_square_1weso(D, T, &weso_cb);
    auto t1 = chrono::high_resolution_clock::now();
    auto td = chrono::duration<double>(t1 - t0).count();
    form y = weso_cb.result;
    form *intermediates = weso_cb.forms.get();  // @@ copy/ref, lifetime = weso_cb
    cout << "[vdf] Result: y.a=" << y.a.impl << " y.b=" << y.b.impl << endl;
    if (td > 0) {
        uint32_t kips = T / td / 1000;
        cout << "[vdf] Computed repeated square. kips=" << kips << endl << flush;
    } else {
        cout << "[vdf] Computed repeated square. Too fast for kIPS calculation." << endl << flush;
    }

    cout << "[vdf] Starting to compute Wesolowski proof." << endl << flush;
    form p = prove_1weso(D, T, y, intermediates);
    cout << "[vdf] Proof: p.a=" << p.a.impl << " p.b=" << p.b.impl << endl;
    cout << "[vdf] Finished computing Wesolowski proof." << endl << flush;

    return vdf_result{y, p};
}

string create_response(integer discriminant, uint64_t iterations, form y, form p) {
    int witness_type = 0;
    int discriminant_bits = discriminant.num_bits();
    // = res[BQFC_FORM_SIZE]; reduce + bqfc_serialize(res, a, b, discriminant_bits);
    // ~ core operator: bqfc_compress(a, b) -> a, t, g, b0, b_sign
    std::vector<uint8_t> y_serialized = SerializeForm(y, discriminant_bits);;
    std::vector<uint8_t> p_serialized = SerializeForm(p, discriminant_bits);;

    std::vector<uint8_t> bytes;
    uint8_t int64_bytes[8];

    // Writes the number of iterations
    Int64ToBytes(int64_bytes, iterations);
    VectorAppendArray(bytes, int64_bytes, sizeof(int64_bytes));

    // Writes the y, with prepended size
    Int64ToBytes(int64_bytes, y_serialized.size());
    VectorAppendArray(bytes, int64_bytes, sizeof(int64_bytes));
    VectorAppend(bytes, y_serialized);

    // Writes the witness type
    bytes.push_back(witness_type);

    // Writes the proof
    VectorAppend(bytes, p_serialized);

    return BytesToStr(bytes);
}

tcp::socket connect_client(boost::asio::io_context& io_context, string host, string port) {
    tcp::socket socket(io_context);
    tcp::resolver resolver(io_context);
    boost::asio::connect(socket, resolver.resolve(host, port, boost::asio::ip::resolver_base::address_configured));
    return socket;
}

bluebox_request read_request(tcp::socket &socket, const optional<string> client_id) {
    char buffer[1024];
    uint64_t size;

    cout << "[net] Reading request." << endl;

    memset(buffer, 0, sizeof(buffer));
    boost::asio::read(socket, boost::asio::buffer(buffer, 1));
    // cout << "[net] Prover type: " << buffer[0] << endl;
    assert (buffer[0] == 'S');

    memset(buffer, 0, sizeof(buffer));
    boost::asio::read(socket, boost::asio::buffer(buffer, 3));
    size = stoull(buffer);
    // cout << "[net] Discriminant size: " << size << endl;

    memset(buffer, 0, sizeof(buffer));
    boost::asio::read(socket, boost::asio::buffer(buffer, size));
    integer discriminant(buffer);
    cout << "[net] Discriminant: D=" << discriminant.impl << endl;

    memset(buffer, 0, sizeof(buffer));
    boost::asio::read(socket, boost::asio::buffer(buffer, 1));
    size = buffer[0];

    memset(buffer, 0, sizeof(buffer));
    boost::asio::read(socket, boost::asio::buffer(buffer, size));
    // initial_form is not used for blueboxing. TODO: debug print nevertheless

    if (client_id) {
        string id = client_id.value();
        assert (id.size() < 256);
        uint8_t len = id.size();
        boost::asio::write(socket, boost::asio::buffer("ID", 2));
        boost::asio::write(socket, boost::asio::buffer(&len, 1));
        boost::asio::write(socket, boost::asio::buffer(id, len));
    } else {
        boost::asio::write(socket, boost::asio::buffer("OK", 2));
    }

    memset(buffer, 0, sizeof(buffer));
    boost::asio::read(socket, boost::asio::buffer(buffer, 2));
    size = stoull(buffer);
    // cout << "[net] Iterations size: " << size << endl;

    memset(buffer, 0, sizeof(buffer));
    boost::asio::read(socket, boost::asio::buffer(buffer, size));
    uint64_t iterations = stoull(buffer);
    cout << "[net] Iterations: T=" << iterations << endl;

    return bluebox_request{discriminant, iterations};
}

void interact_ping(tcp::socket& socket) {
    cout << "[net] Sending PING." << endl;
    boost::asio::write(socket, boost::asio::buffer("PING", 4));

    char buffer[1024];
    boost::asio::read(socket, boost::asio::buffer(buffer, 4));
    assert (strncmp(buffer, "PONG", 4) == 0);
    cout << "[net] Received PONG." << endl;
}

void write_response(tcp::socket& socket, string& res) {
    uint8_t res_size[4];
    Int32ToBytes(res_size, res.size());
    boost::asio::write(socket, boost::asio::buffer(res_size, 4));
    boost::asio::write(socket, boost::asio::buffer(res.c_str(), res.size()));

    cout << "[net] Sending STOP." << endl;
    boost::asio::write(socket, boost::asio::buffer("STOP", 4));

    cout << "[net] Waiting for ACK." << endl;
    char buffer[1024];
    boost::asio::read(socket, boost::asio::buffer(buffer, 3));
    assert (strncmp(buffer, "ACK", 3) == 0);

    cout << "[net] Sent response." << endl;
}

void dump_response(string &res) {
    uint8_t res_size[4];
    Int32ToBytes(res_size, res.size());

    cout << "[net] Response: size=0x";
    {
        auto flags = cout.flags();
        cout << hex << setfill('0')
            << setw(2) << +res_size[0]
            << setw(2) << +res_size[1]
            << setw(2) << +res_size[2]
            << setw(2) << +res_size[3];
        cout.flags(flags);
    }
    cout << " data=" << res << endl;
}

int run_vdf(int argc, char *argv[]) {
    integer D(argv[2]);
    uint64_t T = atoi(argv[3]);

    cout << "Discriminant: D=" << D.impl << endl;
    cout << "Iterations: T=" << T << endl;

    vdf_result r = vdf_1weso(D, T);

    string res = create_response(D, T, r.y, r.p);
    dump_response(res);

    return 0;
}

int run_client(int argc, char *argv[]) {
    auto host = argv[2];
    auto port = argv[3];
    auto client_id = argc > 3 ? optional<string>{argv[4]} : nullopt;

    boost::asio::io_context io_context;
    tcp::socket socket = connect_client(io_context, host, port);

    bluebox_request req = read_request(socket, client_id);

    future<vdf_result> vdf_future = async(vdf_1weso, ref(req.discriminant), req.iterations);
    future_status vdf_status;
    do {
        switch (vdf_status = vdf_future.wait_for(chrono::minutes(3)); vdf_status) {
            case future_status::timeout: interact_ping(socket); break;
        }
    } while (vdf_status != future_status::ready);
    vdf_result r = vdf_future.get();

    string res = create_response(req.discriminant, req.iterations, r.y, r.p);
    dump_response(res);

    write_response(socket, res);

    return 0;
}

int main(int argc, char *argv[]) try {
    if (argc < 3 || (argv[1][0] != 'p' && argv[1][0] != 'c')) {
        cerr << "Usage: " << argv[0] << " <mode> <args>" << endl;
        cerr << "  " << argv[0] << " p <discriminant> <iterations>" << endl;
        cerr << "  " << argv[0] << " c <host> <port> [<client_id>]" << endl;
        return 64;
    }

    init_gmp();
    if (hasAVX2()) {
        gcd_base_bits = 63;
        gcd_128_max_iter = 2;
    }
    set_rounding_mode();

    switch (argv[1][0]) {
    case 'p':
        return run_vdf(argc, argv);
    case 'c':
        return run_client(argc, argv);
    }
    cerr << "nyi" << endl;
    return 64;
} catch (exception &e) {
    cerr << "[cli] Exception: " << e.what() << endl;
    return 1;
}

// TODO: better cli parsing
// TODO: progress! (bar?), new proto
// TODO: proper logging?
// TODO: looped client? (would make timelord-launcher obsolete)
