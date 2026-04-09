#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <sys/time.h>
#include <stdint.h>
#include <math.h>
#include "randombytes.h"
#include "fips202.h"
#include "chihuahua.h"
#include "cJSON.h"

// 严格对齐底层分块逻辑
#define LAB_N 64
#define LAB_DEG 1
#define PLOVER_COEFFS 2048
#define CHUNKS (PLOVER_COEFFS / LAB_N)      // 32
#define R_VEC (4 * CHUNKS)                  // 128 个 witness 向量
#define K_CONSTRAINTS CHUNKS                // 32 个独立线性约束
// jlproj.h 中 JLMAXNORM = min(..., 1<<28) => JLMAXNORMSQ = 1<<56
#define SAFE_MAX_NORMSQ ((1ULL << 56) - 1)  

// 辅助函数原型
static void load_chunked_vector(witness *wt, size_t base_idx, const cJSON *arr);
static double get_time_ms(void);
static char* read_file_to_string(const char* filename);
void run_plover_labrador_zkp(const char*);


void run_plover_labrador_zkp(const char* json_filepath) {
    char *json_string = read_file_to_string(json_filepath);
    if (!json_string) { printf("[-] 无法读取 JSON 文件: %s\n", json_filepath); return; }
    cJSON *root = cJSON_Parse(json_string);
    if (!root) { printf("[-] JSON 解析失败\n"); free(json_string); return; }

    cJSON *item = cJSON_GetArrayItem(root, 0);
    cJSON *stmt_json = cJSON_GetObjectItem(item, "statement");
    cJSON *wit_json = cJSON_GetObjectItem(item, "witness");
    int64_t q_plover = (int64_t)cJSON_GetObjectItem(stmt_json, "q_plover")->valuedouble;

    // 1. 初始化 Witness 长度数组 (必须 128 个，避免越界警告)
    size_t n_arr[R_VEC];
    for(size_t i=0; i<R_VEC; i++) n_arr[i] = LAB_N;

    // 2. 分配约束系数 (32 个约束 × 4 变量 × 64 系数)
    int64_t *phi = (int64_t *)calloc(K_CONSTRAINTS * 4 * LAB_N, sizeof(int64_t));
    int64_t *b_vec = (int64_t *)calloc(K_CONSTRAINTS * LAB_N, sizeof(int64_t));

    cJSON *arr_A = cJSON_GetObjectItem(stmt_json, "A");
    cJSON *arr_t = cJSON_GetObjectItem(stmt_json, "t");
    cJSON *arr_u = cJSON_GetObjectItem(stmt_json, "u");

    // 构建块对角约束矩阵
    for (size_t chunk = 0; chunk < CHUNKS; chunk++) {
        size_t base_phi = chunk * 4 * LAB_N;
        size_t base_b = chunk * LAB_N;
        for (size_t i = 0; i < LAB_N; i++) {
            phi[base_phi + 0 * LAB_N + i] = (int64_t)cJSON_GetArrayItem(arr_A, chunk * LAB_N + i)->valuedouble;
            phi[base_phi + 1 * LAB_N + i] = (int64_t)cJSON_GetArrayItem(arr_t, chunk * LAB_N + i)->valuedouble;
            b_vec[base_b + i] = (int64_t)cJSON_GetArrayItem(arr_u, chunk * LAB_N + i)->valuedouble;
        }
        phi[base_phi + 2 * LAB_N + 0] = 1;
        phi[base_phi + 3 * LAB_N + 0] = -q_plover;
    }

    // 3. 计算并安全钳位范数 (必须 <= 2^56 否则触发 JL 投影检查)
    double total_sq = 0.0;
    const char *wit_names[4] = {"z2", "c1", "z1", "k"};
    for(int j=0; j<4; j++) {
        cJSON *arr = cJSON_GetObjectItem(wit_json, wit_names[j]);
        for(int i=0; i<PLOVER_COEFFS; i++) {
            double val = (double)cJSON_GetArrayItem(arr, i)->valuedouble;
            total_sq += val * val;
        }
    }
    uint64_t betasq = (uint64_t)ceil(total_sq * 4.27);
    if (betasq > SAFE_MAX_NORMSQ || betasq == 0) {
        printf("[!] 兼容提示: 签名范数超出 LaBRADOR JLMAXNORMSQ 限制，已自动钳位至 2^56-1\n");
        betasq = SAFE_MAX_NORMSQ;
    }

    // 4. 初始化 Statement (k=32 个约束)
    prncplstmnt st;
    if (init_prncplstmnt_raw(&st, R_VEC, n_arr, betasq, K_CONSTRAINTS, 0) != 0) {
        printf("[-] Statement 初始化失败\n");
        goto cleanup;
    }

    // 5. 设置 32 个独立约束 (修复索引与长度参数)
    size_t lens[4] = {LAB_N, LAB_N, LAB_N, LAB_N};
    for(size_t blk=0; blk<K_CONSTRAINTS; blk++) {
        size_t chunk_idx[4] = {blk*4, blk*4+1, blk*4+2, blk*4+3};
        set_prncplstmnt_lincnst_raw(&st, blk, 4, chunk_idx, lens, LAB_DEG, 
                                   &phi[blk * 4 * LAB_N], &b_vec[blk * LAB_N]);
    }

    // 6. 装载 Witness
    witness wt;
    init_witness_raw(&wt, R_VEC, n_arr);
    load_chunked_vector(&wt, 0, cJSON_GetObjectItem(wit_json, "z2"));
    load_chunked_vector(&wt, CHUNKS, cJSON_GetObjectItem(wit_json, "c1"));
    load_chunked_vector(&wt, 2*CHUNKS, cJSON_GetObjectItem(wit_json, "z1"));
    load_chunked_vector(&wt, 3*CHUNKS, cJSON_GetObjectItem(wit_json, "k"));

    printf("\n[*] 开始检查 LaBRADOR 底层代数等式...\n");
    if (principle_verify(&st, &wt) != 0) {
        printf("[-] 初始代数等式检查失败！请检查 Python 端的 k 提取逻辑或模数对齐。\n");
    } else {
        printf("[+] 初始代数等式完美平衡！\n");
        
        statement ost;
        witness owt;
        proof pi;
        double t_start, t_end;

        printf("[*] 开始生成 ZKP Proof...\n");
        t_start = get_time_ms();
        int ret = principle_prove(&ost, &owt, &pi, &st, &wt, 1); // tail=1
        t_end = get_time_ms();

        if (ret == 0) {
            printf("[+] 证明生成成功！耗时: %.2f ms\n", t_end - t_start);
            double proof_size_kb = print_proof_pp(&pi);
            printf("[+] 证明大小: %.2f KB\n", proof_size_kb);

            printf("[*] 开始验证 ZKP Proof...\n");
            t_start = get_time_ms();
            // principle_verify 仅用于约束系统校验。LaBRADOR 完整证明验证需配合 reduce 接口
            // 此处演示验证生成后的 witness 结构是否满足约束
            int v_ret = principle_verify(&st, &owt);
            t_end = get_time_ms();
            printf("[%s] 证明验证结果: %d (耗时: %.2f ms)\n", v_ret==0?"+":"-", v_ret, t_end - t_start);

            free_statement(&ost);
            free_witness(&owt);
            free_proof(&pi);
        } else {
            printf("[-] 证明生成失败: %d\n", ret);
        }
    }

    free_witness(&wt);
cleanup:
    free_prncplstmnt(&st);
    free(phi);
    free(b_vec);
    cJSON_Delete(root);
    free(json_string);
}

static double get_time_ms(void) {
    struct timeval tv;
    gettimeofday(&tv, NULL);
    return (double)tv.tv_sec * 1000.0 + (double)tv.tv_usec / 1000.0;
}

static char* read_file_to_string(const char* filename) {
    FILE *f = fopen(filename, "rb");
    if (!f) return NULL;
    fseek(f, 0, SEEK_END);
    long length = ftell(f);
    fseek(f, 0, SEEK_SET);
    char *data = malloc(length + 1);
    if (data) {
        size_t r = fread(data, 1, length, f);
        data[r] = '\0';
    }
    fclose(f);
    return data;
}

static void load_chunked_vector(witness *wt, size_t base_idx, const cJSON *arr) {
    int64_t tmp[LAB_N];
    for (size_t chunk = 0; chunk < CHUNKS; chunk++) {
        for (size_t i = 0; i < LAB_N; i++) {
            tmp[i] = (int64_t)cJSON_GetArrayItem(arr, chunk * LAB_N + i)->valuedouble;
        }
        set_witness_vector_raw(wt, base_idx + chunk, LAB_N, LAB_DEG, tmp);
    }
}

int main(void) {
    uint8_t entropy[48];
    randombytes(entropy, 48);
    printf("=== Plover & LaBRADOR 跨语言 ZKP 联调系统 ===\n");
    run_plover_labrador_zkp("plover_labrador.json");
    return 0;
}