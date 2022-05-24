#include <iostream>
#include <optional>

#include <aws/core/Aws.h>
#include <aws/sqs/SQSClient.h>
#include <aws/sqs/model/ChangeMessageVisibilityRequest.h>
#include <aws/sqs/model/DeleteMessageRequest.h>
#include <aws/sqs/model/GetQueueUrlRequest.h>
#include <aws/sqs/model/GetQueueUrlResult.h>
#include <aws/sqs/model/ReceiveMessageRequest.h>
#include <aws/sqs/model/ReceiveMessageResult.h>
#include <aws/sqs/model/SendMessageRequest.h>
#include <aws/sqs/model/SendMessageResult.h>
#include <boost/asio.hpp>
#include <rapidjson/document.h>
#include <rapidjson/stringbuffer.h>
#include <rapidjson/writer.h>

#include "vdf.h"
#include "create_discriminant.h"


using namespace std;
using namespace std::chrono;
using namespace std::literals::chrono_literals;


int gcd_base_bits = 50;
int gcd_128_max_iter = 3;


struct vdf_result {
    // TODO?: add D, T
    form y;
    form p;
};


void repeated_square_1weso(const integer& D, uint64_t T, WesolowskiCallback* weso) {
    vdf_original vdfo;
    integer L = root(-D, 4);
    form x = form::generator(D);

    uint64_t num_iterations = 0;
    while (num_iterations <= T) {
        uint64 batch_size = checkpoint_interval;

        // Overall throughput for blueboxing significantly increases if we run
        // one single-threaded worker per CPU (hyper-)thread, instead of one
        // dual-threaded worker per every two CPU (hyper-)threads.
        square_state_type square_state{.pairindex = 0};
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
    cout << "[vdf] Computing repeated square x^2^" << T
        << " for x with discriminant " << D.impl << "."
        << endl << flush;

    form x = form::generator(D);
    cout << "[vdf] Base: x.c=" << x.c.impl << endl;
    OneWesolowskiCallback weso_cb(D, x, T);
    auto t0 = high_resolution_clock::now();
    repeated_square_1weso(D, T, &weso_cb);
    auto t1 = high_resolution_clock::now();
    auto td = duration<double>(t1 - t0).count();
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

string enhex(const vector<uint8_t> cs) {
    stringstream res;
    res << "0x" << hex << setfill('0') ;
    for (unsigned c : cs) {
        res << setw(2) << c;
    }
    return res.str();
}

vector<uint8_t> dehex(const string& hexstr) {
    vector<uint8_t> res;
    auto i = (hexstr.length() > 2 && hexstr[0] == '0' && hexstr[1] == 'x') ? 2 : 0;
    for (; i < hexstr.length(); i += 2) {
        res.push_back(strtol(hexstr.substr(i, 2).c_str(), nullptr, 16));
    }
    return res;
}

rapidjson::Document make_response(const rapidjson::Document& request, vdf_result result) {
    using namespace rapidjson;

    auto p_serialized = SerializeForm(result.p, /*discriminant_bits*/1024);
    auto p_hex = enhex(p_serialized);

    Document response;
    response.CopyFrom(request, response.GetAllocator()); // Copies header_hash, height, field_vdf.

    auto vdf_info = response.FindMember("new_proof_of_time"); // Rename new_proof_of_time to vdf_info.
    vdf_info->name.SetString("vdf_info", response.GetAllocator());

    Value vdf_proof(kObjectType); // Create new vdf_proof object.
    vdf_proof.AddMember("witness_type", Value(0), response.GetAllocator());
    vdf_proof.AddMember("witness", Value(p_hex.c_str(), p_hex.size(), response.GetAllocator()), response.GetAllocator());
    vdf_proof.AddMember("normalized_to_identity", Value(true), response.GetAllocator());
    response.AddMember("vdf_proof", vdf_proof, response.GetAllocator());

    return response;
}

string json_dumps(const rapidjson::Document& doc) {
    rapidjson::StringBuffer buffer;
    rapidjson::Writer<rapidjson::StringBuffer> writer(buffer);
    doc.Accept(writer);
    return buffer.GetString();
}

int run_vdf() {
    const auto discriminant = getenv("DISCRIMINANT");
    if (!discriminant) {
        cerr << "[cli] No discriminant passed. Set DISCRIMINANT environment variable." << endl;
    }
    const auto iterations = getenv("ITERATIONS");
    if (!iterations) {
        cerr << "[cli] No iterations passed. Set ITERATIONS environment variable." << endl;
    }
    if (!discriminant || !iterations) {
        return 1;
    }

    integer D(discriminant);
    uint64_t T = atoi(iterations);

    vdf_result r = vdf_1weso(D, T);

    return 0;
}

int run_sqs() {
    //const auto max_workers = atoi(getenv("VDF_CLIENT_WORKERS"));
    const auto client_id = getenv("VDF_CLIENT_ID");
    if (!client_id) {
        cerr << "[cli] Client ID not configured. Set VDF_CLIENT_ID environment variable." << endl;
        return 1;
    }

    Aws::SQS::SQSClient sqs;

    const auto todo_url = "https://bluebox.xchdata.io/635745634815/bluebox-todo.fifo";
    const auto done_url = "https://bluebox.xchdata.io/635745634815/bluebox-done.fifo";

    cout << "[sqs] Polling to receive uncompact part." << endl;
    const auto rm_req = Aws::SQS::Model::ReceiveMessageRequest()
        .WithQueueUrl(todo_url)
        .WithMaxNumberOfMessages(1)  // @@ number of free workers
        .WithWaitTimeSeconds(20);
    const auto rm_out = sqs.ReceiveMessage(rm_req);
    if (!rm_out.IsSuccess()) {
        cerr << "[sqs] Error receiving uncompact part: " << rm_out.GetError().GetMessage() << endl;
        return 1;
    }

    const auto& todo_messages = rm_out.GetResult().GetMessages();
    if (todo_messages.size() == 0) {
        cerr << "[sqs] Finished, no uncompact part received." << endl;
        return 0;
    }
    const auto& todo_message = todo_messages[0];
    const auto todo_body = todo_message.GetBody();
    cout << "[sqs] Received uncompact part: " << todo_body << endl;

    rapidjson::Document todo_doc;
    todo_doc.Parse(todo_body.c_str());

    auto challenge = dehex(todo_doc["new_proof_of_time"]["challenge"].GetString());
    integer D = CreateDiscriminant(challenge);
    uint64_t T = todo_doc["new_proof_of_time"]["number_of_iterations"].GetUint64();

    const auto heartbeat_timeout = 1min;
    const auto visibility_timeout = 2 * heartbeat_timeout;
    future<vdf_result> vdf_future = async(vdf_1weso, ref(D), T);
    future_status vdf_status;
    do {
        switch (vdf_status = vdf_future.wait_for(heartbeat_timeout); vdf_status) {
            case future_status::timeout:
                const auto cmv_req = Aws::SQS::Model::ChangeMessageVisibilityRequest()
                    .WithQueueUrl(todo_url)
                    .WithReceiptHandle(todo_message.GetReceiptHandle())
                    .WithVisibilityTimeout(duration_cast<seconds>(visibility_timeout).count());
                const auto cmv_out = sqs.ChangeMessageVisibility(cmv_req);
                if (!cmv_out.IsSuccess()) {
                    cerr << "[sqs] Error sending ping: "
                        << cmv_out.GetError().GetMessage() << endl;
                    return 1;
                }
                cout << "[sqs] Sent ping." << endl;
                break;
        }
    } while (vdf_status != future_status::ready);
    vdf_result result = vdf_future.get();

    const auto json_result = json_dumps(make_response(todo_doc, result));
    const auto sm_req = Aws::SQS::Model::SendMessageRequest()
        .WithQueueUrl(done_url)
        .WithMessageGroupId(client_id)  // @@ good idea?
        .AddMessageAttributes("Xchdata.ClientId",
                Aws::SQS::Model::MessageAttributeValue()
                    .WithDataType("String")
                    .WithStringValue(client_id))
        .WithMessageBody(json_result);
    const auto sm_out = sqs.SendMessage(sm_req);
    if (!sm_out.IsSuccess()) {
        cerr << "[sqs] Error sending compact part: " << sm_out.GetError().GetMessage() << endl;
        return 1;
    }
    cout << "[sqs] Sent compact part: " << json_result << endl;

    const auto dm_req = Aws::SQS::Model::DeleteMessageRequest()
        .WithQueueUrl(todo_url)
        .WithReceiptHandle(todo_message.GetReceiptHandle());
    const auto dm_out = sqs.DeleteMessage(dm_req);
    if (!dm_out.IsSuccess()) {
        cerr << "[sqs] Error deleting uncompact part "
            << todo_message.GetMessageId() << ": "
            << dm_out.GetError().GetMessage() << endl;
    }
    cout << "[sqs] Finished, deleted uncompact part." << endl;

    return 0;
}

int main(int argc, char *argv[]) try {
    if (argc < 2 || string::npos == "pq"s.find(argv[1][0])) {
        cerr << "Usage: " << argv[0] << " <mode>" << endl;
        cerr << "  DISCRIMINANT=<discriminant> ITERATIONS=<iterations> " << argv[0] << " p" << endl;
        cerr << "  VDF_CLIENT_ID=<client_id>                           " << argv[0] << " q" << endl;
        return 64;
    }

    init_gmp();
    if (hasAVX2()) {
        gcd_base_bits = 63;
        gcd_128_max_iter = 2;
    }
    set_rounding_mode();

    if ('p' == argv[1][0]) {
        return run_vdf();
    }
    if ('q' == argv[1][0]) {
        Aws::SDKOptions options;
        Aws::InitAPI(options);
        auto rc = run_sqs();
        Aws::ShutdownAPI(options);
        return rc;
    }
    cerr << "[cli] Unreachable!" << endl;
    return 64;
} catch (exception &e) {
    cerr << "[cli] Exception: " << e.what() << endl;
    return 1;
}

// TODO: progress! (bar?), new proto
// TODO: proper logging?
// TODO: looped client? (would make timelord-launcher obsolete)

// vim: set ts=4 sw=4 et:
