#ifndef CLICK_TINYNF_HH
#define CLICK_TINYNF_HH

#include <click/element.hh>
#include <click/task.hh>

#include "env/pci.h"

#include <atomic>
#include <map>
#include <tuple>

struct tn_pci_device_comparer {
  bool operator()(const struct tn_pci_device& a, const struct tn_pci_device& b) const {
    return std::tie(a.bus, a.device, a.function) < std::tie(b.bus, b.device, b.function);
  }
};

CLICK_DECLS
class TinyNF : public Element {
  public:
    TinyNF() CLICK_COLD;
    ~TinyNF() CLICK_COLD;
    const char *class_name() const { return "TinyNF"; }
    const char *port_count() const { return PORTS_1_1; }
    const char *processing() const { return PUSH; }
    int configure(Vector<String> &, ErrorHandler *) override CLICK_COLD;
    int initialize(ErrorHandler *) override CLICK_COLD;
    bool run_task(Task *) override;
    void push(int port, Packet *p) override;
  private:
    static struct tn_net_device* get_device(String addr);
    static void packet_destructor(unsigned char* buffer, size_t size, void* arg);
    static std::map<tn_pci_device, tn_net_device*, tn_pci_device_comparer> _devices;
    static std::atomic<int> _instance_count;
    struct tn_net_agent* _agent;
    Task _task;
    bool _killing;
};
CLICK_ENDDECLS
#endif
